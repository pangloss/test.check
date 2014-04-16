(ns clojure.test.check.simulate
  (:import (java.io Writer))
  (:require [clojure.pprint :refer [pprint]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :refer [for-all*]]
            [clojure.test.check.rose-tree :as rose]
            [clojure.math.combinatorics :refer [combinations]]))

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

; Simulation runs in 2 phases. First we generate command lists, then we execute
; them. The state machine is used during both phases, first to enable
; generation of commands that affect previous results, then to validate actual
; results against simulated state.

; When generating commands, we call next-state on state machine without
; executing any command. In place of that command's result, we use a Var
; instance which the state may treat as a black box representing the result.
; The state machine may store those vars to use them for future command
; generation or verification.  So we might have (MyState. #{(Var. 1) (Var. 2)}
; {:x (Var. 1)}) after some commands have been generated.

; Each var is numbered and permanantly associated to its command. Even when
; some commands are removed during shrinking, the var numbers associated with
; the command will not change.
;
; Once a test is completely generated, it is passed to the runner which
; executes each command, this time passing the actual result of running the
; command to the state machine's `next-state` as well as `postcondition` or
; `error?` functions. Any vars in commands must refer to previously executed
; statements, and so before that statement is executed, any vars in the command
; are replaced with the corresponding value.
;
; If an exception is thrown or the `error?` or `postcondition` functions
; indicate a bad state, the test has failed and now moves into the shrinking
; stage.
;
; When shrinking, we first minimize the number of commands needed to reproduce,
; then attempt to shrink the arguments those commands are given. To do that we
; again use the state machine. Each command subset is validated to ensure that
; all vars a command refers to will exist in the subset, then to ensure that
; the state preconditions should be expected to pass. This can greatly reduce
; the number of invalid tests generated.

(defmacro state-command [state idx bindings commands]
  (let [commands (mapv (fn [[cond command]] `(when ~cond ~command)) commands)
        commands (condp = (count bindings)
                   1 `(let [~(first bindings) ~state] ~commands)
                   2 `(let [~(first bindings) ~state ~(second bindings) (Var. :init)] ~commands)
                   (assert false "Generate commands with either [state] or [state-map initial-value-var] bindings."))]
    `(let [commands# (->> ~commands (filter identity) vec)]
       (when (seq commands#)
         (nth commands# (mod ~idx (count commands#)))))))

(defn get-command* [op-rose]
  (second (rose/root op-rose)))

(defn- unchunk
  "Borrowed from math.combinatorics"
  [s]
  (lazy-seq
   (when (seq s)
     (cons (first s) (unchunk (rest s))))))

(defn subsets-rose [items]
  [items
   (mapcat (fn [n]
             (map (comp subsets-rose vec)
                  (combinations items n)))
           (unchunk (reverse (range 1 (count items)))))])

(defn shrink-operations* [{:keys [initial-state precondition next-state]} op-roses]
  ; Build a custom rose tree that more effectively searches the space
  ; - search pairs then triples, etc.
  ; - relative sequence is preserved
  ; - discard combinations where a var used by one command is not available
  ; - understand preconditions and skip compositions with failing ones
  ; - shrink size before changing any arguments
  (let [size (count op-roses)
        init-var (Var. :init)]
    (->> (subsets-rose (range (count op-roses)))
         (rose/fmap
           (fn [indices]
             (let [selected-roses (mapv #(nth op-roses %) indices)
                   operations (map rose/root selected-roses)
                   available-var (conj (set (map first operations)) init-var)
                   commands (map second operations)
                   used-vars (filter #(instance? Var %) (tree-seq coll? seq commands))]
               (when (and (every? available-var used-vars)
                          (or (not precondition)
                              (reduce (fn [state [var command]]
                                        (if (precondition state command)
                                          (next-state state command var)
                                          (reduced nil)))
                                      (assoc (initial-state) :shrink true)
                                      operations)))
                 ; Hopefully this does the following:
                 ; each rose should be [operations [less operations ...
                 ;                                  shrunk operations ...]]
                 ; first shrink by number of commands. If we pass all of those, shrink by operations
                 (rose/zip vector selected-roses)))))
         rose/join
         (rose/filter identity))))

; - generate a vector of positive ints
; - inside the state loop, working through those ints:
;   - generate a command corresponding to the int given the current state.
;   - the command may have generators embedded.
;   - Turn the command into its own rose tree so that the command's arguments can be shrunk.
;   - use the root version of the command to progress to the next state
; - we now have a list of rose trees, one for each command.
; - combine those commands into one rose tree for this test which follows the ideas set out in shrink-operations*
(defmacro gen-operations [sim bindings & commands]
  ; TODO:
  ; - Allow a literal prefix of commands for setup to be passed in. Never shrunk.
  (assert (even? (count commands)) "Incorrect condition command pair.")
  (let [commands (partition 2 commands)]
    `(let [sim# ~sim
           initial-state# (:initial-state sim#)
           next-state# (:next-state sim#)
           max-op-size# (:max-size sim# 50)]
       (assert (fn? initial-state#) "Simulation must specify :initial-state function")
       (assert (fn? next-state#) "Simulation must specify :next-state function")
       (gen/make-gen
         (fn [rnd# size#]
           (let [gen-indices# (->> gen/pos-int gen/no-shrink gen/vector gen/no-shrink
                                   (gen/such-that not-empty))
                 indices# (rose/root (gen/call-gen gen-indices# rnd# size#))
                 [op-roses# _# _#]
                 (reduce (fn [[op-roses# state# counter#] idx#]
                           (let [var# (make-var counter#)
                                 command# (state-command state# idx# ~bindings ~commands)
                                 operation# [var# command#]
                                 operation-rose# (gen/call-gen (gen/literal operation#) rnd# (mod size# max-op-size#))]
                             [(conj op-roses# operation-rose#)
                              (next-state# state# (get-command* operation-rose#) var#)
                              (inc counter#)]))
                         [[] (initial-state#) 0]
                         indices#)]
             (shrink-operations* sim# op-roses#)))))))

(defn eval-command [target vars [method f args]]
  ; TODO:  search deeper within the structure for vars to replace.
  (let [f' (if (and (not= :custom method) (symbol? f))
             (eval f)
             f)
        args (mapv #(if (instance? Var %) (get vars %) %) args)]
    [(try
       (condp = method
         :apply (apply f' args)
         :-> (apply f' target args)
         :->> (apply f' (concat args [target]))
         :custom (target vars [f args]))
       (catch Throwable t t))
     [method f args]]))

(defn on-error [{:keys [error cause] :as data}]
  (let [message (cond
                  error (str "Error detected: " error)
                  (instance? Throwable cause) (str "Simulation exception: " (.getMessage ^Throwable cause))
                  :else "Postcondition failed")
        data (select-keys data [:var :state :target :result :command])]
    (if cause
      (throw (ex-info message data cause))
      (throw (ex-info message data)))))

(defn error? [state command result]
  (when (instance? Throwable result)
    (.getMessage ^Throwable result)))

(defn runner
  "Required: initial-state next-state
   Optional:
     precondition - default to no precondition
     postcondition - default to no checks for bad state after command execution and state transition
     error? - default to no checks for bad state after command execution and state transition
   _
   If included, precondition must return true for the command to be executed. It's
   useful for general state checks and also to validate functions when shrinking and some
   setup may have been removed.
   _
   postcondition or error? are interchangeable. error? allows you to return an
   actual error message, while postcondition just returns true if the state is
   ok, which is easier to write!
   _
   Optional behaviour configuration:
     reduce - allows you to switch between reduce and reductions
     on-error - default throws ex-info
     eval-command - [`f [:as args]] -> (apply f args)"
  [{:keys [initial-state precondition next-state postcondition] :as sim}]
  (assert (fn? initial-state) "Simulation must specify :initial-state function")
  (assert (fn? next-state) "Simulation must specify :next-state function")
  (let [eval-command (get sim :eval-command eval-command)
        on-error (get sim :on-error on-error)
        error? (get sim :error? error?)
        initial-target (get sim :initial-target (constantly nil))
        reduce (get sim :reduce reduce)]
    (fn [operations]
      (let [init-target (initial-target)
            vars (atom {(Var. :init) init-target}) ]
        (reduce
          (fn [[state target :as ignore] [v command]]
            (try
              (if (or (not precondition)
                      (precondition state command))
                (let [[result command'] (eval-command target @vars command)
                      state' (next-state state command' result)]
                  (try
                    (let [failed (when postcondition (not (postcondition state' command' result)))
                          error (error? state' command' result)]
                      (swap! vars assoc v result)
                      (if (or error failed)
                        (on-error {:error error :var v :vars @vars :fail operations
                                   :pre-state state :state state'
                                   :pre-command command :command command'
                                   :target target :result result})
                        [state' result]))
                    (catch Throwable t
                      (if (:state (ex-data t))
                        (throw t)
                        (on-error {:var v :vars @vars :fail operations
                                   :pre-state state :state state'
                                   :pre-command command :command command'
                                   :target target :result result :cause t})))))
                ignore)
              (catch Throwable t
                (if (:state (ex-data t))
                  (throw t)
                  (on-error {:var v :vars @vars :fail operations :state state
                             :command command :target target :cause t})))))
          [(initial-state) init-target]
          operations)))))

(defn simulator* [sim sim-gen]
  (for-all* [sim-gen] (runner sim)))

(defmacro simulator
  "See arguments to runner and gen-operations."
  [sim & stuff]
  `(let [sim# ~sim
         ops# (gen-operations sim# ~@stuff)]
     (assoc (simulator* sim# ops#)
            :gen-operations ops#)))
