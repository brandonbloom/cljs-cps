(ns cps
  (:require [cljs.compiler :as comp]
            [cljs.analyzer :as ana]))

(use '[clojure.pprint :only (pprint)])
(defmacro dbg [x]
  `(let [x# ~x]
    (binding [*out* *err*]
       (println "<<<<<<<<<<<<")
       (pprint '~x)
       (println "============")
       (pprint x#)
       (println ">>>>>>>>>>>")
     x#)))

(def ^:dynamic *k* nil)

(defn call-cc* [f & args]
  (assert false))

(defmacro call-cc [f & args]
  (when-not *k*
    (throw (Exception. "call-cc must be used within a cps transform")))
  `(call-cc* ~@(next &form)))

(defmacro with-cc [k & body]
  `(call-cc (fn [~k] ~@body)))

(defmacro return [k value]
  (when-not *k*
    (throw (Exception. "return must be used within a cps transform")))
  (list 'cps/-return k value))

(defmacro raise [k error]
  (when-not *k*
    (throw (Exception. "raise must be used within a cps transform")))
  (list 'cps/-raise k error))

(defmacro update-return [k f]
  `(Continuation. ~f (.raisef ~k)))

(defmacro with-raise [k f]
  `(Continuation. (.returnf ~k) ~f))

(def control-ops `#{call-cc call-cc*})

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

;;TODO: Nearly all use of metadata in analyze causes data loss when transformed

(defmulti anf
  "Applies an Administrative Normal Form transformation to an AST.
  The transformation is selective with regard to trivial expressions."
  :op)

(def anf* (comp :form anf))

(defmethod anf :default
  [{:keys [env op] :as ast}]
  (when-not (#{:ns :var :constant :deftype* :defrecord*} op)
    (ana/warning env (str "Unsupported op " op " in ANF transform")))
  ast)

(defn- anf-application [{:keys [env] :as ast} key f]
  (let [args (key ast)]
    (if (every? trivial? args)
      ast
      (let [syms (repeatedly (count args) #(gensym "anf__"))
            forms (map anf* args)]
        (ana/analyze env `(let* [~@(interleave syms forms)]
                            ~(f syms)))))))

(defmethod anf :invoke
  [{:keys [f] :as ast}]
  (if (control-op? f)
    (anf-application ast :args #(cons (:form f) %))
    (anf-application ast :children identity)))

(defmethod anf :new
  [{:keys [form] :as ast}]
  (anf-application ast :args #(concat (take 2 form) %)))

(defmethod anf :throw
  [ast]
  (anf-application ast :children #(cons 'throw %)))

(defmethod anf :recur
  [ast]
  (anf-application ast :exprs #(cons 'recur %)))

(defmethod anf :map
  [ast]
  (anf-application ast :children #(apply hash-map %)))

(defmethod anf :vector
  [ast]
  (anf-application ast :items vec))

(defmethod anf :set
  [ast]
  (anf-application ast :items set))

(defmethod anf :js
  [{:keys [env form] :as ast}]
  (anf-application ast :args #(concat (take 2 form) %)))

(defmethod anf :set!
  [{:keys [env target val] :as ast}]
  (if (trivial? val)
    ast
    (ana/analyze env `(let* [val# ~(anf* val)]
                        (set! ~(:form target) val#)))))

(defmethod anf :if
  [{:keys [env test then else] :as ast}]
  (let [then (anf* then)
        else (when else [(anf* else)])]
    (ana/analyze env (if (trivial? test)
                       `(if ~(:form test) ~then ~@else)
                       `(let* [test# ~(anf* test)]
                          (if test# ~then ~@else))))))

;;TODO: Test this! Turns out that it's tricky to work around the reader.
(defmethod anf :meta
  [{:keys [env meta expr children] :as ast}]
  (if (every? trivial? children)
    ast
    ;NOTE: funky expr/meta evaluation order matches emit phase
    (ana/analyze env `(let* [expr# ~(anf* expr)
                             meta# ~(anf* meta)]
                        (cljs.core/with-meta expr# meta#)))))

(defn- anf-block
  [{:keys [statements ret] :as ast}]
  (when ast
    (let [children (conj (vec statements) ret)]
      (map anf* children))))

(defmethod anf :do
  [{:keys [env] :as ast}]
  (ana/analyze env `(do ~@(anf-block ast))))

(defmethod anf :try*
  [{:keys [env try catch name finally] :as ast}]
  (ana/analyze env `(~'try*
                     ~@(anf-block try)
                     ~@(when catch
                         (list (list* 'catch name
                                      (anf-block catch))))
                     ~@(when finally
                         (list (cons 'finally
                                     (anf-block finally)))))))

(defn- anf-bindings
  [{:keys [env bindings form] :as ast}]
  (ana/analyze env `(~(first form)
                        [~@(mapcat (fn [{:keys [name init]}]
                                     [name (anf* init)])
                                   bindings)]
                        ~@(anf-block ast))))

(defmethod anf :let
  [ast]
  ;;TODO Handle loop
  (anf-bindings ast))

(defmethod anf :letfn
  [ast]
  (anf-bindings ast))

(defmethod anf :dot
  [{:keys [env target field method form] :as ast}]
  (if (serious? target)
    (anf (ana/analyze env `(let* [target# ~(:form target)]
                             (~'. target# ~@(drop 2 form)))))
    (if field
      ast
      (anf-application ast :args #(concat (take 3 form) %)))))

(defmethod anf :def
  [{:keys [env init form] :as ast}]
  (if (trivial? init)
    ast
    (ana/analyze env `(let* [init# ~(anf* init)]
                        (~@(butlast form) init#)))))

(defmethod anf :fn
  [{:keys [env form methods] :as ast}]
  (let [prefix (first (split-with (complement seq?) form))]
    (ana/analyze env `(~@prefix ~@(map (fn [{:keys [form] :as method}]
                                         `(~(first form) ~@(anf-block method)))
                                       methods)))))



;; CPS STUFF BELOW

(defmulti cps
  "Applies a Continuation Passing Style transformation to an AST.
  The transformation is selective with regard to trivial expressions and
  assumes that serious expressions are in Administrative Normal Form."
  :op)

(def cps* (comp :form cps))

(defn- wrap-return
  [{:keys [env form] :as ast}]
  (if (= (:context env) :return)
    (ana/analyze env `(cps/return ~*k* ~form))
    ast))

(defmethod cps :default
  [{:keys [env op] :as ast}]
  (when-not (#{:ns :var :constant :js :deftype* :defrecord*
               :new :map :vector :set :set! :if :meta :dot} op)
    (ana/warning env (str "Unsupported op " op " in CPS transform")))
  (wrap-return ast))

(defn- cps-block
  [{:keys [env statements ret] :as ast}]
  (when ast
    (let [children (conj (vec statements) ret)]
      (if (every? trivial? children)
        (conj (mapv :form statements) (:form (wrap-return ret)))
        ;; Inject a let binding for serious statements and CPS transform that.
        (let [[trivials [serious & more]] (split-with trivial? children)
              sym (gensym "result__")
              let-form `(let* [~sym ~(:form serious)]
                         ~@(if more
                             (map :form more)
                             [sym]))
              let-ast (ana/analyze (:env serious) let-form)]
          (conj (mapv :form trivials) (cps* let-ast)))))))

(defmethod cps :do
  [{:keys [env] :as ast}]
  (ana/analyze env `(do ~@(cps-block ast))))

(defmethod cps :invoke
  [{:keys [env form] :as ast}]
  (when (serious? ast)
    (throw (Error. "TODO: Does this ever happen? move :invoke to :default ?")))
  ast)

(def ^:private make-binding (juxt :name #(:form (:init %))))

(defmethod cps :let
  [{:keys [env bindings form statements ret] :as ast}]
  ;;TODO handle loop
  (let [[trivials [serious & more :as deferred]] (split-with #(trivial? (:init %)) bindings)]
    (if serious
      (let [serious-env (-> serious :init :env)
            body (map :form (conj (vec statements) ret))]
        (cond
          (seq trivials)
            ;; Isolate trivial bindings into a separate let.
            (ana/analyze env
              `(let [~@(mapcat make-binding trivials)]
                 ~(cps* (ana/analyze serious-env
                          `(let [~@(mapcat make-binding deferred)]
                             ~@body)))))
          (seq more)
            ;; Isolate the first serious binding into it's own let.
            (cps (ana/analyze env
                   `(let ~(make-binding serious)
                      (let [~@(mapcat make-binding more)]
                        ~@body))))
          (= (:op (:init serious)) :invoke)
            ;; Call with current continuation, binding result to argument.
            (let [k (gensym "k__")
                  body (binding [*k* k]
                         (cps* (ana/analyze serious-env `(do ~@body))))
                  arg (:name serious)
                  k-form `(update-return ~*k* (fn* [~k ~arg] ~@(next body)))
                  [control-op f & args] (-> serious :init :form)]
              (assert (= control-op 'cps/call-cc*))
              (ana/analyze env
                `(~f ~k-form ~@args)))
          :else
            ;; Collapse outer lets into tail position of inner lets.
            (let [name (:name serious)
                  {:keys [op bindings statements ret env]} (:init serious)]
              (dbg op)
              (assert (= op :let))
              (cps (ana/analyze serious-env
                     `(let* [~@(mapcat make-binding bindings)]
                        ~@(map :form statements)
                        (let* [~name ~(:form ret)]
                          ~@body)))))))
      (ana/analyze env
        `(~@(take 2 form) ~@(cps-block ast))))))


;;TODO: Rename this? This name implies to me a (js/setTimeout 0 f)
(defmacro spawn
  "Transforms body into the continuation passing style and evaluates it.
  Evaluation is initially synchronous, but may utilize continuation control
  forms to schedule asynchronous evaluations. Execution resumes outside the
  spawn form immediately after the synchronous portion of body yields."
  [& body]
  (when *k*
    (throw (Exception. "spawn may only be used outside of a cps transform.")))
  (binding [*k* 'cps/top-level-k]
    (-> (ana/analyze &env `(do ~@(next &form)))
        (assoc-in [:env :context] :statement)
        anf cps :form)))


;;TODO ALL THE OPS!
;(defmethod cps :throw
;(defmethod cps :def
;(defmethod cps :fn
;(defmethod cps :try*
;(defmethod cps :let           ; if loop, use trampoline-like thing
;(defmethod cps :letfn
;(defmethod cps :recur

;TODO: Optimize continuations in tail positions.


(comment

(def repl-env
  (binding [ana/*cljs-ns* 'cljs.user]
    (-> (ana/empty-env)
        (ana/analyze '(ns cps-repl
                        (:require-macros [cps :refer (call-cc)])))
        :env
        (assoc :ns (ana/get-namespace ana/*cljs-ns*)))))

(def ^:dynamic *k* 'cps/top-level-k)

(defn analyze [form]
  (ana/analyze repl-env form))

(trivial? (analyze 'x))

(trivial? (analyze '(call-cc identity)))

(trivial? (analyze '(defn f [x] x)))

(trivial? (analyze '(defn f [] (cps/call-cc identity))))

(trivial? (analyze '(defn f [] (call-cc identity))))

(defmacro go [form]
  (let [ast (assoc-in (analyze form) [:env :context] :return)
        ast' (anf ast)
        p #(-> % :form pprint)]
    (println "\n\nANF:\n")
    (p ast')
    (println "\nCPS:\n")
    (p (cps ast'))
    (println "\n")))

(go 1)

(go (identity 1))

(go (identity 1 (call-cc 2) 3 (call-cc 4)))

(go (Integer. 1))

(go (Integer. (call-cc 1)))

(go (set! x 1))

(go (set! x (call-cc 1)))

(go (set! x (identity (call-cc 1))))

(go (if 1 2))

(go (if 1 2 3))

(go (if (call-cc 1) 2 3))

(go (if 1 (identity (call-cc 2)) 3))

(go (if (call-cc 1) (identity (call-cc 2)) 3))

(go {:x 1})

(go {(call-cc 1) 2})

(go [1])

(go [(call-cc 1)])

(go #{1})

(go #{(call-cc 1)})

(go (throw 1))

(go (throw (call-cc 1)))

(go (do))

(go (do 1 2 3))

(go (do
      1
      (identity (call-cc 2))
      3))

(go (let [x 1]
      (identity x)))

(go (let [x (identity (call-cc 1))]
     2))

(go '(let [x 1]
       (identity (call-cc 2))))

(go (try 1))

(go (try (throw (call-cc 1))))

(go (try 1 (catch Error e 2)))

(go (try 1 (finally 2)))

(go (try 1 (catch Error e 2) (finally 3)))

(go (try 1
      (catch Error e (identity (call-cc 2)))
      (finally (identity (call-cc 3)))))

(go (.f 1 2))

(go (.f (call-cc 1) 2))

(go (.f 1 (call-cc 2)))

(go (def x 1))

(go (def x (call-cc 1)))

(go (fn [x] x))

(go (fn ([x] x) ([x y] x)))

(go (fn [x] (identity (call-cc x))))

(go (fn ([x] (identity (call-cc x)))
        ([x y] (identity (call-cc x y)))))

(go (js* "~{} + ~{}" 1 2))

(go (js* "~{} + ~{}" 1 (call-cc f)))

(go (letfn [(f [x] x)] (f 1)))

(go (letfn [(f [x] (identity (call-cc x)))] (f 1)))

(go (deftype T [x] P (f [x] x)))

(go (deftype T [x] P (f [x] (identity (call-cc x)))))

(go (defrecord R [x] P (f [x] x)))

(go (defrecord R [x] P (f [x] (identity (call-cc x)))))

(go (do x (call-cc y) z))

(go (do x (w (call-cc y)) z))

(go (do
      (print \A)
      (print (call-cc (fn [k] (return k \B))))
      (print \C)))


(go (do (call-cc f)))

(go (do a (call-cc b) c))

(go (do a (x (call-cc b)) c))                                ;;;;TODO: FIXME!

(go (do a (x (call-cc b) y) c))                                ;;;;TODO: FIXME!

(go (let [x 1
          y (let [z (call-cc b)
                  w (f z)]
              w)]
      (g x y)))

(let [a 1
      b (let [x 2]
          (+ a x))
      c 3]
  (+ a b c))

(let [a 1]
  (let [b (let [x 2]
            foo
            (+ a x))]
    (let [c 3]
      (+ a b c))))

(let [a 1]
  (let [x 2]
    foo
    (let [b (+ a x)]
      (let [c 3]
        (+ a b c)))))


(go (identity 1 (call-cc 2) 3 (call-cc 4)))

(go (call-cc f))

(go (f (call-cc g 1)))

(go (f (call-cc (fn [x] x))))

(go (let [x (call-cc f 1)] x))

(go (let [x 1
          y (call-cc f 2 3)
          z 4]
      (+ x y z)))

(go (do
      (print \A)
      (print (call-cc (fn [k] (return k \B))))
      (print \C)))

)
