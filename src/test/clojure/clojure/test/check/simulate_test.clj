(ns clojure.test.check.simulate-test
  (:use clojure.test)
  (:require [clojure.test.check :as tc]
            [clojure.core.match :refer [match]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.simulate :refer [simulator gen-operations]]
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
     (fn [{:keys [transient]} [_ f _]]
       (condp = f
         (`conj `disj `transient) (not transient)
         (`conj! `disj! `persistent!) transient
         true))
     :next-state
     (fn [state command result]
       (let [state (assoc state :target result)]
         (match
           command
           [_ `make-set _] state
           [_ `transient [_]] (assoc state :transient true)
           [_ `persistent! [_]] (assoc state :transient false)
           [_ `conj [_ v]] (update-in state [:contents] assoc v true)
           [_ `disj [_ v]] (update-in state [:contents] dissoc v)
           [_ `conj! [_ v]] (update-in state [:contents] assoc v true)
           [_ `disj! [_ v]] (update-in state [:contents] dissoc v))))
     :error?
     (fn [{:keys [contents] :as state} [_ f [target arg]] result]
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
    (not target) [:apply `make-set []]
    (and target (not transient)) [:apply `conj [target gen/int]]
    (and target (not transient) (seq contents)) [:apply `disj [target (gen/elements (vec (keys contents)))]]
    (and target (not transient)) [:apply `transient [target]]
    (and target transient) [:apply `persistent! [target]]
    (and target transient) [:apply `conj! [target gen/int]]
    (and target transient (seq contents)) [:apply `disj! [target (gen/elements (vec (keys contents)))]]))


(defspec transient-state-test 10000 test-set)
