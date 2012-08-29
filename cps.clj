(ns cps
  (:require [cljs.compiler :as comp]
            [cljs.analyzer :as ana]))

;; TODO: Put this into the env
;(def ^:dynamic *k* 'cps/top-level-k)

(defmacro call-cc [f & args]
  (throw (Exception. "call-cc must be used within a cps transform")))

(defmacro return [k value]
  (throw (Exception. "return must be used within a cps transform")))

(defmacro raise [k error]
  (throw (Exception. "raise must be used within a cps transform")))

(def control-ops `#{call-cc return raise})

(defn control-op?
  [{:keys [op info] :as ast}]
  (and (= op :var) (contains? control-ops (:name info))))

;;TODO: Possible optimization: annontation pass, this becomes O(1)
;; Downside: Must manually re-run annotation pass when re-creating forms.
;; Could potentially bypass downside with pluggable hooks in base analyze.
(defn serious?
  "Serious expressions might evaluate one or more control forms."
  [{:keys [op f children] :as ast}]
  (or (and (= op :invoke) (control-op? f))
      (boolean (some serious? children))))

(defn trivial?
  "Trivial expressions definitely do not evaluate any control forms."
  [ast]
  (not (serious? ast)))

(defmulti anf
  "Applies an Administrative Normal Form transformation to an AST.
  The transformation is selective with regard to trivial expressions."
  :op)

(defmethod anf :default
  [{:keys [env op] :as ast}]
  (when-not (#{:var} op)
    (ana/warning env (str "Unsupported op " op " in ANF transform")))
  ast)

(defn- anf-application [env prefix args]
  (let [syms (repeatedly (count args) #(gensym "anf"))
        forms (map (comp :form anf) args)]
    (ana/analyze env `(let [~@(interleave syms forms)]
                        (~@(map :form prefix) ~@syms)))))


(defmethod anf :invoke
  [{:keys [env children f args] :as ast}]
  (if (control-op? f)
    (if (every? trivial? args)
      ast
      (anf-application env [f] args))
    (if (trivial? ast)
      ast
      (anf-application env [] children))))

;;TODO ALL THE OPS!
;(defmethod cps :meta
;(defmethod cps :map
;(defmethod cps :vector
;(defmethod cps :set
;(defmethod cps :constant
;(defmethod cps :if
;(defmethod cps :throw
;(defmethod cps :def
;(defmethod cps :fn
;(defmethod cps :do
;(defmethod cps :try*
;(defmethod cps :let
;(defmethod cps :recur
;(defmethod cps :new
;(defmethod cps :set!
;(defmethod cps :ns
;(defmethod cps :deftype*
;(defmethod cps :defrecord*
;(defmethod cps :dot
;(defmethod cps :js

(defn- wrap-return
  [{:keys [env context] :as ast} k]
  (if (and k (= context :return))
    (ana/analyze env `(k-return ~k)
    k)))

(defmulti cps
  "Applies a Continuation Passing Style transformation to an AST.
  The transformation is selective with regard to trivial expressions and
  assumes that serious call-sites are in Administrative Normal Form."
  (fn [ast k]
    (:op ast)))

(defmethod cps :default
  [{:keys [env op] :as ast} k]
  ;;TODO: Error? Generic walk? Something else? See also anf :default
  (ana/warning env (str "Unsupported op " op " in CPS transform"))
  ast)

(defmethod cps :invoke
  [{:keys [env f args] :as ast} k]
  (if (trivial? ast)
    ast
    nil))

;;TODO ALL THE OPS!
;(defmethod cps :invoke
;(defmethod cps :var
;(defmethod cps :meta
;(defmethod cps :map
;(defmethod cps :vector
;(defmethod cps :set
;(defmethod cps :constant
;(defmethod cps :if
;(defmethod cps :throw
;(defmethod cps :def
;(defmethod cps :fn
;(defmethod cps :do
;(defmethod cps :try*
;(defmethod cps :let
;(defmethod cps :recur
;(defmethod cps :new
;(defmethod cps :set!
;(defmethod cps :ns
;(defmethod cps :deftype*
;(defmethod cps :defrecord*
;(defmethod cps :dot
;(defmethod cps :js

;(defmacro anf*
;  "Applies a selective ANF transform to a form."
;  [form]
;  (-> (ana/analyze &env form) anf :form))
;
;(defmacro cps*
;  "Applies a selective CPS transform to a form."
;  [form]
;  (-> (ana/analyze &env form) anf (cps nil) :form))

(comment

(defn analyze [form]
  (ana/analyze (ana/empty-env) form))

(use '[clojure.pprint :only (pprint)])

(trivial? (analyze '(defn f [x] x)))

(trivial? (analyze '(defn f [] (cps/call-cc identity))))

(defn show-anf [form]
  (-> form
    analyze
    anf
    :form
    pprint))


(show-anf '(identity 1))

(show-anf '(identity 1 (cps/call-cc 2) 3 (cps/call-cc 4)))

;TODO? (trivial? (analyze '(do (defn ^:cps f [x] x) (f 1))))

)
