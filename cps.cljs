(ns cps
  (:require-macros [cps :only (call-cc)]))

(defprotocol IContinuation
  ;;TODO: Should these start with a dash and be considered "internal"?
  (return [_ result])
  (raise [_ error]))

(deftype Continuation [returnf raisef]
  IContinuation
  (return [_ result]
    (returnf result))
  (raise [_ error]
    (raisef error)))

(defn continuation? [x]
  (instance? Continuation x))

(def top-level-k
  (Continuation. identity #(throw %)))
