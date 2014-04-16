(ns clojure.test.check.simulate-test
  (:use clojure.test)
  (:require [clojure.test.check :as tc]
            [clojure.set :refer [map-invert]]
            [clojure.core.match :refer [match]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.simulate :refer [simulator gen-operations simulator*]]
            [clojure.test.check.clojure-test :as ct :refer (defspec)]))

(defn incorrect? [s result]
  (when-not (:t? s)
    (not= (into #{} (keys (:contents s))) result)))

(defn transient?  [x]
  (instance? clojure.lang.ITransientCollection x))

(def test-set
  (simulator
    {:initial-state
     (fn initial-state [] {:contents {} :t? false})
     :initial-target
     (fn initial-target [] #{})
     :precondition
     (fn pre [{:keys [shrink t?]} [_ f _]]
       (condp = f
         `conj        (not t?)
         `disj        (not t?)
         `transient   (not t?)
         `conj!       t?
         `disj!       t?
         `persistent! t?))
     :next-state
     (fn next-state [state command result]
       (match
         command
         [_ `transient []] (assoc state :t? true)
         [_ `persistent! []] (assoc state :t? false)
         [_ `conj [v]] (update-in state [:contents] assoc v true)
         [_ `disj [v]] (update-in state [:contents] dissoc v)
         [_ `conj! [v]] (update-in state [:contents] assoc v true)
         [_ `disj! [v]] (update-in state [:contents] dissoc v)))
     :error?
     (fn error? [{:keys [contents] :as state} [_ f [arg]] result]
       (when (set? result)
         (condp = f
           `conj
           (cond (not= arg (result arg)) (str "Argument `" arg "` should be present in the result")
                 (incorrect? state result) "Expected state does not match result")
           `conj!
           (cond (not= arg (result arg)) (str "Argument `" arg "` should be present in the result")
                 (incorrect? state result) "Expected state does not match result")
           `disj
           (when (incorrect? state result) "Expected state does not match result")
           `disj!
           (when (incorrect? state result) "Expected state does not match result")
           `transient
           (when (not (transient? result)) "Result should be transient")
           `persistent!
           (when (transient? result) "Result should not be transient"))))}
    [{:keys [contents t?]}]
    (not t?) [:-> `conj [gen/int]]
    (and (not t?) (seq contents)) [:-> `disj [(gen/elements (vec (keys contents)))]]
    (not t?) [:-> `transient []]
    t? [:-> `persistent! []]
    t? [:-> `conj! [gen/int]]
    (and t? (seq contents)) [:-> `disj! [(gen/elements (vec (keys contents)))]]))


; With size > 100, this will almost certainly fail on Clojure 1.5.1:
(defspec transient-state-test 200 test-set)

(comment

  (tc/quick-check 1000 test-set)

  )


; =======================================================================================
; =======================================================================================
; This example is reproducing an example from erlang and isn't meant to be run beyond
; just generating the tests.

(defrecord State [^java.util.Set pids
                  ^java.util.Map regs
                  ^java.util.Set killed])

(def sim-config
  {:initial-state (fn initial-state [] (State. #{} {} #{}))
   :next-state
   (fn next-state [{:keys [killed regs] :as state} command result]
     (match command
            [_ `spawn _] (update-in state [:pids] conj result)
            [_ `kill [pid]] (-> state
                                (update-in [:killed] conj pid)
                                (update-in [:regs] #(dissoc % ((map-invert %) pid))))
            [_ `reg [n pid]] (if (and (not (killed pid))
                                      (not (regs n)))
                               (assoc-in state [:regs n] pid)
                               state)
            [_ `unreg [n]] (update-in state [:regs] dissoc n)
            [_ `proc_reg/where [n]] state
            :else (do (println "Unmatched command:")
                      (prn command)
                      state)))
   :postcondition
   (fn postcondition [{:keys [regs]} command result]
     (match [command result]
            [[_ `reg [n pid]] true] (not (regs n))
            [[_ `reg [n pid]] [:sim/exit _]] (regs n)
            [[_ `unreg [n]] true] (regs n)
            [[_ `unreg [n]] [:sim/exit _]] (not (regs n))
            [[_ `where [n]] _] (= (regs n) result)
            :else true))})


; result is a black box because it may be a result or it may be a var object
; when generating tests. Args that are generated from results are the same.


(def sim-gen
  (gen-operations
    sim-config
    [{:keys [pids regs] :as state}]
    true       [:apply `spawn []]
    (seq pids) [:apply `kill  [(gen/elements (vec pids))]]
    (seq pids) [:apply `reg [(gen/resize 1 gen/keyword) (gen/elements (vec pids))]]
    true       [:apply `unreg [(if (seq regs)
                                 (gen/one-of [(gen/resize 1 gen/keyword)
                                              (gen/elements (vec (keys regs)))])
                                 (gen/resize 1 gen/keyword))]]
    true       [:apply `proc_reg/where [(if (seq regs)
                                          (gen/one-of [(gen/resize 1 gen/keyword)
                                                       (gen/elements (vec (keys regs)))])
                                          (gen/resize 1 gen/keyword))]]))


(comment

  ; FIXME: not all generators are being evaluated...
  (clojure.pprint/pprint
    (gen/sample
      sim-gen
      10))

  (gen/call-gen sim-gen (gen/random) 0)

  )

