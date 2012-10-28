(ns cps
  (:require-macros [cps :refer (call-cc)]))

(defprotocol IContinuation
  (-return [_ result])
  (-raise [_ error]))

(deftype Continuation [returnf raisef]
  IContinuation
  (-return [k result]
    (try*
      (returnf result)
      (catch e
        (-raise k e))))
  (-raise [k error]
    (raisef error)))

(defn continuation? [x]
  (instance? Continuation x))

(def top-level-k
  (Continuation. (fn [result] nil)
                 (fn [error] (throw error))))
