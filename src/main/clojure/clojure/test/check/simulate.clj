(ns clojure.test.check.simulate
  (:import (java.io Writer))
  (:require [clojure.pprint :refer [pprint]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :refer [for-all*]]
            [clojure.test.check.rose-tree :as rose]
            [clojure.math.combinatorics :refer [subsets]]))

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

(defmacro state-command [state idx bindings commands]
  `(let [commands# (let [~(first bindings) ~state] ~(mapv (fn [[cond command]] `(when ~cond ~command)) commands))
         commands# (->> commands# (filter identity) vec)]
     (when (seq commands#)
       (nth commands# (mod ~idx (count commands#))))))

; current:

; generate list of ints
; bind that to the state transformer which creates commands
; - the state machine is given unevaluated generators which does not work well (undo tree...)
; the rose tree is based on the command indices rather than the generated commands

; should:

; generate list of ints
; use state machine to turn that into list of (gen/literal operations)
; build a rose tree (with my own shrink algorithm? (first shrink command list, then shrink args))

; search spaces were manageable in original naive version so it is possible. Don't completely
; understand why my search space is so large...

(defn get-command* [op-rose]
  (second (rose/root op-rose)))

(defn get-var* [op-rose]
  (first (rose/root op-rose)))

(defn shrink-operations* [{:keys [initial-state precondition next-state]} op-roses]
  ; Build a custom rose tree that more effectively searches the space
  ; - search pairs then triples, etc.
  ; - relative sequence is preserved
  ; - discard combinations where a var used by one command is not available
  ; - understand preconditions and skip compositions with failing ones
  ; - shrink size before changing any arguments
  (let [size (count op-roses)]
    [(map rose/root op-roses)
     (for [indices (subsets (range (count op-roses)))
           :when (> size (count indices) 0)
           :let [selected-roses (mapv #(nth op-roses %) indices)
                 operations (map rose/root selected-roses)
                 available-var (set (map first operations))
                 commands (map second operations)
                 used-vars (filter #(instance? Var %) (tree-seq coll? seq commands))]
           :when (every? available-var used-vars)
           :when (or (not precondition)
                     (reduce (fn [state [var command]]
                               (if (precondition state command)
                                 (next-state state command var)
                                 (reduced nil)))
                             (assoc (initial-state) :shrink true)
                             operations))]
       (rose/zip vector selected-roses))]))

(defmacro gen-operations [sim bindings & commands]
  ; TODO:
  ; - Allow a literal prefix of commands for setup to be passed in. Never shrunk.
  (assert (even? (count commands)) "Incorrect condition command pair.")
  (let [commands (partition 2 commands)]
    `(let [sim# ~sim
           initial-state# (:initial-state sim#)
           next-state# (:next-state sim#)]
       (assert (fn? initial-state#) "Simulation must specify :initial-state function")
       (assert (fn? next-state#) "Simulation must specify :next-state function")
       (gen/make-gen
         (fn [rnd# size#]
           ; cycle size within 5 and 55 for the command list
           (let [gen-indices# (->> gen/pos-int gen/no-shrink gen/vector gen/no-shrink
                                   (gen/such-that not-empty))
                 indices# (rose/root (gen/call-gen gen-indices# rnd# size#))
                 [op-roses# _# _#]
                 (reduce (fn [[op-roses# state# counter#] idx#]
                           (let [var# (make-var counter#)
                                 command# (state-command state# idx# ~bindings ~commands)
                                 ; keep the rose for each command and mix it into the rose generator below the
                                 ; list pairing operations
                                 operation# [var# command#]
                                 operation-rose# (gen/call-gen (gen/literal operation#) rnd# size#)]
                             [(conj op-roses# operation-rose#)
                              (next-state# state# (get-command* operation-rose#) var#)
                              (inc counter#)]))
                         [[] (initial-state#) 0]
                         indices#)]
             (shrink-operations* sim# op-roses#)))))))

(defn eval-command [target vars [method f args]]
  (try
    ; TODO:  search deeper within the structure for vars to replace.
    (let [f (eval f)
          args (map #(if (instance? Var %) (get vars %) %) args)]
      (condp = method
        :apply (apply f args)
        :-> (apply f target args)
        :->> (apply f (concat args [target]))
        :custom (f target vars args)))
    (catch Throwable t t)))

(defn on-error [{:keys [error] :as data}]
  (throw (ex-info (str "Postcondition failed: " error)
                  (select-keys data [:var :operations :post-state]))))

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
  [{:keys [initial-state precondition next-state error? postcondition] :as sim}]
  (assert (fn? initial-state) "Simulation must specify :initial-state function")
  (assert (fn? next-state) "Simulation must specify :next-state function")
  (let [eval-command (get sim :eval-command eval-command)
        on-error (get sim :on-error on-error)
        error? (get sim :error? error?)
        initial-target (get sim :initial-target (constantly nil))
        reduce (get sim :reduce reduce)
        vars (atom {})]
    (fn [operations]
      (reduce
        (fn [[state target :as ignore] [v command]]
          (if (or (not precondition) (precondition state command))
            (let [result (eval-command target @vars command)
                  state' (next-state state command result)
                  failed (when postcondition (not (postcondition state' command result)))
                  error (error? state' command result)]
              (swap! vars assoc v result)
              (if (or error failed)
                (on-error {:error error :var v :vars @vars :operations operations
                           :pre-state state :post-state state' :command command :result result})
                [state' result]))
            ignore))
        [(initial-state) (initial-target)]
        operations))))

(defn simulator* [sim sim-gen]
  (for-all* [sim-gen] (runner sim)))

(defmacro simulator
  "See arguments to runner and gen-operations."
  [sim & stuff]
  `(let [sim# ~sim
         ops# (gen-operations sim# ~@stuff)]
     (assoc (simulator* sim# ops#)
            :gen-operations ops#)))
