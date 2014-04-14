(ns clojure.test.check.simulate-test
  (:use clojure.test)
  (:require [clojure.test.check :as tc]
            [clojure.set :refer [map-invert]]
            [clojure.core.match :refer [match]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.simulate :refer [simulator gen-operations simulator*]]
            [clojure.test.check.clojure-test :as ct :refer (defspec)]))

(defn incorrect? [s result]
  (when-not (:transient s)
    (not= (into #{} (keys (:contents s))) result)))

(defn transient?  [x]
  (instance? clojure.lang.ITransientCollection x))

(defn make-set [] #{})

(def test-set
  (simulator
    {:initial-state
     (fn [] {:contents {} :transient false})
     :precondition
     (fn [{:keys [transient]} [f _]]
       (condp = f
         (`conj `disj `transient) (not transient)
         (`conj! `disj! `persistent!) transient
         true))
     :next-state
     (fn [state command result]
       (let [state (assoc state :target result)]
         (match
           command
           [`make-set _] state
           [`transient [_]] (assoc state :transient true)
           [`persistent! [_]] (assoc state :transient false)
           [`conj [_ v]] (update-in state [:contents] assoc v true)
           [`disj [_ v]] (update-in state [:contents] dissoc v)
           [`conj! [_ v]] (update-in state [:contents] assoc v true)
           [`disj! [_ v]] (update-in state [:contents] dissoc v))))
     :error?
     (fn [{:keys [contents] :as state} [f [target arg]] result]
       (if (not= (count result) (count contents))
         "Counts not equal"
         (condp = f
           (`conj `conj!)
           (cond (not (result arg)) "Argument should be present in the result"
                 (incorrect? state result) "Expected state does not match result")
           (`disj `disj!)
           (when (incorrect? state result) "Expected state does not match result")
           `transient
           (when (not (transient? result)) "Result should be transient")
           `persistent!
           (when (transient? result) "Result should not be transient")
           nil))) }
    [{:keys [target contents transient]}]
    (not target) [`make-set []]
    (and target (not transient)) [`conj [target gen/int]]
    (and target (not transient) (seq contents)) [`disj [target (gen/elements (vec (keys contents)))]]
    (and target (not transient)) [`transient [target]]
    (and target transient) [`persistent! [target]]
    (and target transient) [`conj! [target gen/int]]
    (and target transient (seq contents)) [`disj! [target (gen/elements (vec (keys contents)))]]))


(defspec transient-state-test 10000 test-set)

(comment

  (tc/quick-check 1000 test-set)

  )


; =======================================================================================
; =======================================================================================

(defrecord State [^java.util.Set pids
                  ^java.util.Map regs
                  ^java.util.Set killed])

(def sim-config
  {:initial-state (fn initial-state [] (State. #{} {} #{}))
   :next-state
   (fn next-state [{:keys [killed regs] :as state} command result]
     (match command
            [`spawn _] (update-in state [:pids] conj result)
            [`kill [pid]] (-> state
                              (update-in [:killed] conj pid)
                              (update-in [:regs] #(dissoc % ((map-invert %) pid))))
            [`reg [n pid]] (if (and (not (killed pid))
                                    (not (regs n)))
                             (assoc-in state [:regs n] pid)
                             state)
            [`unreg [n]] (update-in state [:regs] dissoc n)
            [`proc_reg/where [n]] state
            :else (do (println "Unmatched command:")
                      (prn command)
                      state)))
   :postcondition
   (fn postcondition [{:keys [regs]} command result]
     (match [command result]
            [[`reg [n pid]] true] (not (regs n))
            [[`reg [n pid]] [:sim/exit _]] (regs n)
            [[`unreg [n]] true] (regs n)
            [[`unreg [n]] [:sim/exit _]] (not (regs n))
            [[`where [n]] _] (= (regs n) result)
            :else true))})


; result is a black box because it may be a result or it may be a var object
; when generating tests. Args that are generated from results are the same.


(def sim-gen
  (gen-operations
    sim-config
    [{:keys [pids regs] :as state}]
    true       [`spawn []]
    (seq pids) [`kill  [(gen/elements (vec pids))]]
    (seq pids) [`reg [(gen/resize 1 gen/keyword) (gen/elements (vec pids))]]
    true       [`unreg [(if (seq regs)
                          (gen/one-of [(gen/resize 1 gen/keyword)
                                       (gen/elements (vec (keys regs)))])
                          (gen/resize 1 gen/keyword))]]
    true       [`proc_reg/where [(if (seq regs)
                                   (gen/one-of [(gen/resize 1 gen/keyword)
                                                (gen/elements (vec (keys regs)))])
                                   (gen/resize 1 gen/keyword))]]))


(comment

  ; FIXME: not all generators are being evaluated...
  (clojure.pprint/pprint
    (gen/sample
      (gen/add-size
        50
        sim-gen)
      1))

  )
