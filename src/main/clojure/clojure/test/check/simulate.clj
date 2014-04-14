(ns clojure.test.check.simulate
  (:import (java.io Writer))
  (:require [clojure.pprint :refer [pprint]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :refer [for-all*]]
            [clojure.set :refer [map-invert]]))

(defrecord Var [n]
  gen/LiteralGenerator
  (literal* [this] (gen/return this)))
(defn make-var [n]
  (Var. n))

(defmethod print-method Var [{:keys [value n]} , ^Writer w]
  (.write w (str "(V " n ")")))
(let [^clojure.lang.MultiFn f clojure.pprint/simple-dispatch]
  (.addMethod f Var pr))
(def V make-var)

; when generating commands, we use the state machine, we don't run the commands, but rather use a "result" proxy like (Var. 1)
; that we pass to next-state as if it were a result. The state machine does what it needs with those vars (if anything). So we
; might have (State. #{(Var. 1) (Var. 2)} {:x (Var. 1)}) when the commands are finished being generated. Because some of the
; commands are generated from the state, they generate may have some of the vars embedded in them.

; Each command has its number attached to it, so that if they are shrunk, the
; numbers don't change.
;
; The next phase is actually running the commands. They are numbered the same, and when the actual results come in, they are
; delivered to the vars promises. When a var is referred to, it is dereferenced and the value is passed in to the command.


(defmacro state-command [state idx bindings commands size]
  `(let [commands# (let [~(first bindings) ~state] ~(mapv (fn [[cond command]] `(when ~cond ~command)) commands))
         commands# (->> commands# (filter identity) vec)]
     (when (seq commands#)
       (->> (nth commands# (mod ~idx (count commands#)))
            gen/literal
            (gen/add-size ~size)
            gen/sample-seq
            first))))

(defmacro gen-operations [sim bindings & commands]
  ; TODO: ensure presence of initial-state and next-state in sim
  (let [commands (partition 2 commands)]
    `(let [sim# ~sim
           initial-state# (:initial-state sim#)
           next-state# (:next-state sim#)]
       (assert (fn? initial-state#) "Simulation must specify :initial-state function")
       (assert (fn? next-state#) "Simulation must specify :next-state function")
       (gen/bind
         ; each item is a vector of integers. Integers will be used modulo the size
         ; of the available command list for the current state.
         (gen/such-that not-empty (gen/vector gen/pos-int))
         (fn [indices#]
           (let [[result# state# counter#]
                 (reduce (fn [[result# state# counter#] idx#]
                           (let [var# (make-var counter#)
                                 command# (state-command state# idx# ~bindings ~commands counter#)
                                 operation# [var# command#]]
                             [(conj result# operation#)
                              (next-state# state# command# var#)
                              (inc counter#)]))
                         [[] (initial-state#) 0]
                         indices#)]
             (gen/return result#)))))))

(defn eval-command [vars [method f args]]
  (try
    (condp = method
      ; TODO:  search deeper within the structure for vars to replace.
      :apply (eval (apply list f (map #(if (instance? Var %) (get vars %) %) args))))
    (catch Throwable t t)))

(defn on-error [{:keys [error] :as data}]
  (throw (ex-info (str "Postcondition failed: " error) data)))

(defn runner [{:keys [initial-state precondition next-state error?] :as sim}]
  "Required: initial-state next-state
   Optional:
     reduce - allows you to switch between reduce and reductions
     precondition - default to no precondition
     error? - default to no checks for bad state after command execution and state transition
     on-error - default throws ex-info
     eval-command - [:apply `f [:as args]] -> (apply f args)"
  (assert (fn? initial-state) "Simulation must specify :initial-state function")
  (assert (fn? next-state) "Simulation must specify :next-state function")
  (let [eval-command (get sim :eval-command eval-command)
        on-error (get sim :on-error on-error)
        reduce (get sim :reduce reduce)
        vars (atom {})]
    (fn [operations]
      (reduce
        (fn [state [v command]]
          (if (or (not precondition) (precondition state command))
            (let [result (eval-command @vars command)
                  state' (next-state state command result)
                  error (when error? (error? state` command result))]
              (swap! vars assoc v result)
              (if error
                (on-error {:error error :var v :vars @vars :operations operations
                           :pre-state state :post-state state' :command command :result result})
                state'))
            state))
        (initial-state)
        operations))))

(defn simulator* [sim sim-gen]
  (for-all* [sim-gen] (runner sim)))

(defmacro simulator [sim & stuff]
  `(let [sim# ~sim]
     (simulator* sim# (gen-operations sim# @~stuff))))

(comment
  ; Example code

  (use '[clojure.walk :only [macroexpand-all]])
  (require '[clojure.test.check :as tc])
  (require '[clojure.core.match :refer [match]])
  (defrecord State [^java.util.Set pids
                    ^java.util.Map regs
                    ^java.util.Set killed])
  (defn initial-state []
    (State. #{} {} #{}))
  ; result is a black box because it may be a result or it may be a var object
  ; when generating tests. Args that are generated from results are the same.
  (defn next-state [{:keys [killed regs] :as state} command result]
    (match command
           [:apply `spawn _] (update-in state [:pids] conj result)
           [:apply `kill [pid]] (-> state
                                    (update-in [:killed] conj pid)
                                    (update-in [:regs] #(dissoc % ((map-invert %) pid))))
           [:apply `reg [n pid]] (if (and (not (killed pid))
                                          (not (regs n)))
                                   (assoc-in state [:regs n] pid)
                                   state)
           [:apply `unreg [n]] (update-in state [:regs] dissoc n)
           [:apply `proc_reg/where [n]] state
           :else (do (println "Unmatched command:")
                     (prn command)
                     state)))
  (defn precondition [state command]
    true)
  (defn error? [{:keys [regs]} command result]
    (match [command result]
           [[:apply `reg [n pid]] true] (not (regs n))
           [[:apply `reg [n pid]] [:sim/exit _]] (regs n)
           [[:apply `unreg [n]] true] (regs n)
           [[:apply `unreg [n]] [:sim/exit _]] (not (regs n))
           [[:apply `where [n]] _] (= (regs n) result)
           :else true))


  (clojure.pprint/pprint
    (gen/sample
      (gen/add-size
        50
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
      1))



  (def sim-config
    {:initial-state initial-state
     :next-state next-state
     :precondition precondition
     :error? error?})

  (simulator*
    sim-config
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

  (simulator
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
                                          (gen/resize 1 gen/keyword))]])

  )

