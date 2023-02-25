(def special-forms 
  [:def
   :var
   :fn
   :do
   :quote
   :if
   :splice
   :while
   :break     
   :set 
   :quasiquote 
   :unquote 
   :upscope]) 

(defn- same-type? [t1 t2]
  (= (t1 :name) (t2 :name)))

(defn- create-type [name]
  {:name name})

(defmacro- create-prim-types [& type-pairs]
  ;(map (fn [tp] ~(def ,(first tp) ,(create-type (last tp)))) type-pairs))

(def Array :array)
(def Tuple :tuple)
(def Indexed :indexed)

(def Table :table)
(def Struct :struct)
(def Dict :dict)

(def Function :function)
(def CFunction :cfunction)

(create-prim-types 
  [String :string]
  [Buffer :buffer]
  [Number :number]
  [Nil :nil]
  [Symbol :symbol]
  [Boolean :boolean]
  [Keyword :keyword]
  [Fiber :fiber]
  [Any :any])

(def- DEFAULT-RECORD
  @{:+ {:name :function :params {:variadic Number} :ret Number}})

(defn- create-type-env [&opt parent]
  @{:parent parent 
    :record DEFAULT-RECORD})

(defn- get-type [type-env key]
  (let [value ((type-env :record) key)
        parent (type-env :parent)]
    (cond 
      (not (nil? value)) value 
      (and (nil? value) (nil? parent)) value 
      (get-type parent key))))

(defn- set-type [type-env key value]
  (put 
    (type-env :record) 
    (if (keyword? key)
      key
      (keyword key)) 
    value))

(defn- extract-metadata 
  ``We're taking an indexed collection and trying to find either a literal type keyword, such as:
       :number 
       :string 
       :buffer 
       :symbol 
       :keyword 
       :boolean 
       :nil
       :any

    Or a struct with key :type and some composed type, such as:
       {:type (-> [:number :number] :number)}
       {:type (dict :keyword :number)}
       {:type (dict {:a :number :b :string})}
       {:type (struct {:x :any :y :buffer})}
  ``
  [metadata]
  (var res nil)
  (each m metadata 
    (each l [Number String Buffer Symbol Keyword Boolean Nil Any]
      (cond 
        (= l m) (set res l)
        (dictionary? m) (set res (m :type)))))
  res)

(defn- assert-type [declared inferred expr]
  (unless (same-type? declared inferred)
    (errorf "\n\tDeclared %p type in %p, but %p is a %p.\n" (declared :name) expr (last expr) (inferred :name))))
        
(defn- tc [type-env expr]
  (defn tc-symbol [te e]
    (get-type te e))

  (defn tc-application [te e]
    `` Gets the type of the form being called, its parameters and its return.
    Throws if the types of the arguments do not align with the types of the parameters, or
    if the type of the return value does not align with the type declared.
    If no return type is declared, it will be inferred.
    If no parameter types are declared, they will be considered Any

    Function types look like this:
        (defn some-fn [num bool &opt thing & name1 name2 name3] num)
        {:name :function 
         :params {:positional [Number Boolean] 
                  :optional [Any] 
                  :variadic String}
         :ret Number}
    ``
    (let [op-type (tc-symbol te (keyword (first e)))
          args (slice e 1)]
      (unless (nil? op-type)
        (let [params-type (op-type :params)
              return-type (op-type :ret)
              positional-params (params-type :positional)
              optional-params (params-type :optional)
              variadic-params (params-type :variadic)
              no-positional-params (nil? positional-params)
              no-optional-params (nil? optional-params)
              no-variadic-params (nil? variadic-params)
              positionalc (if no-positional-params 0 (length positional-params))
              optionalc (if no-optional-params 0 (length (params-type :optional)))
              variadic-start (+ positionalc optionalc)]
          (unless no-positional-params
            (eachp [i pos-arg] (slice args 0 positionalc)
              (assert-type (get positional-params i) (tc te pos-arg) e)))
          (unless no-optional-params
            (eachp [i opt-arg] (slice args positionalc variadic-start)
              (assert-type (get optional-params i) (tc te opt-arg) e)))
          (unless no-variadic-params
            (each var-arg (slice args variadic-start)
              (print "Var arg: " var-arg "\tInferred: " (tc te var-arg))
              (assert-type variadic-params (tc te var-arg) e)))))))

  (defn tc-do [te e]
    (var res nil)
    (each inner-expr (slice e 1)
      (set res (tc te inner-expr)))
    res)

  (defn tc-def [te e]
    (let [lhs (get e 1)
          declared-type (create-type (extract-metadata (slice e 2 -1)))
          inferred-type (tc te (last e))]
      (if (not (nil? (declared-type :name)))
        (assert-type declared-type inferred-type e))
      (set-type te lhs inferred-type)
      inferred-type))

  (defn tc-tuple [te e]
    (let [ef (macex e)]
      (case (keyword (get ef 0))
        :do (tc-do te ef)
        :def (tc-def te ef)
        (tc-application te ef))))
    
  (let [expr-type (type expr)]
    (case expr-type
      # :table (walk-dict f $f)
      # :struct (table/to-struct (walk-dict f $f))
      # :array (walk-ind f $f)
      :symbol (tc-symbol type-env expr)
      :tuple (tc-tuple type-env expr)
      (create-type expr-type))))

(defmacro type-check
  ``Infers and validates the type of an expression.``
  [expr]
  (let [te (create-type-env)]
    (printf "Type env initialized: %p" (te :record))
    (tc te expr)))

(comment 
  (def x :number 10)
  (def f 
    :private 
    # :number 
    {:type (-> [:number :number] :number)}
    (fn [a b]
      (+ a b)))
  
  (same-type? String String)
  (same-type? String Number)
  
  (assert-type Number String '(def x :number "10"))
  
  (extract-metadata '(:a :b :number))
  (extract-metadata [:a :b {:type :number}])
  (extract-metadata [:a :b])

  (type-check 10)
  (type-check "string")
  (type-check @"buffer")
  (type-check (def x 10))
  (type-check (do 
                (def x 10)
                @"yolo"))

  (type-check (+ 1 2))
  (type-check (+ 1 "yo"))

  (type-check '(1 2 3))

  (create-type-env)

  (def test-te (create-type-env))
  (tc test-te (def x 6))
  (tc test-te (def y x))

  (type-check (def x :string 10))
  (type-check (defn add [a b] (+ a b)))
  (type-check (if true true false)))