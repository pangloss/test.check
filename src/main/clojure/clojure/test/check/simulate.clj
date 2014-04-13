(ns clojure.test.check.simulate
  (:import (java.io Writer))
  (:require
            [clojure.test.check.generators :as gen]
            [clojure.set :refer [map-invert]]))

(defrecord Var [n value]
  gen/LiteralGenerator
  (literal* [this] (gen/return this)))
(defn make-var
  ([n] (Var. n (promise)))
  ([n value] (Var. n (deliver (promise) value))))

(defmethod print-method Var [{:keys [value n]} , ^Writer w]
  (.write w (if (realized? value)
              (str "(V " n ", " (pr-str @value) ")")
              (str "(V " n ")"))))
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

(defmacro gen-states [init-state next-state bindings & commands]
  (let [commands (partition 2 commands)]
    `(gen/bind
       ; each item is a vector of integers. Integers will be used modulo the size
       ; of the available command list for the current state.
       (gen/such-that not-empty (gen/vector gen/pos-int))
       (fn [indices#]
         (let [[result# state# counter#]
               (reduce (fn [[result# state# counter#] idx#]
                         (let [command# (state-command state# idx# ~bindings ~commands counter#)]
                           [(conj result# command#)
                            (~next-state state# command# (make-var counter#))
                            (inc counter#)]))
                       [[] (~init-state) 0]
                       indices#)]
           (gen/return result#))))))



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

  (clojure.pprint/pprint
    (take 1 (drop 50 (gen/sample-seq
      (gen-states
        initial-state
        next-state
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
                                              (gen/resize 1 gen/keyword))]]
        )
                       ))))



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
  (defn runner []
    (run-commands (initial-state) next-command next-state precondition error?))

  )


(comment
  ; possibly needed...

  (defn exec-command [state command]
    (match command
           [:apply f args]
           {:result (eval (apply list f (map #(if (:var (meta %)) (% state) %) args)))
            :state state}
           [:set v subcommand]
           (let [result (:result (exec-command state subcommand))]
             {:state (update-in state [:var v] result)
              :result result})))

  (defn run-commands [initial next-command next-state precondition postcondition]
    'ok)



  (defn simulate-actions [s coll actions]
    (reduce
      (fn [[s value] [action arg]]
        (if (pre action s)
          (let [result (next-value action s value arg)
                s' (next-state action s value arg) ]
            (if-let [error (error? action s' result arg)]
              (throw (ex-info (str "Postcondition failed: " error)
                              {:pre-state s :post-state s' :action action :arg arg
                               :value value :result result}))
              [s' result]))
          [s value]))
      [s coll]
      actions))
  )
