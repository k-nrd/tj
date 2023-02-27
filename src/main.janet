(def special-forms 
  [:fn
   :quote
   :if
   :splice
   :while
   :break     
   :quasiquote 
   :unquote 
   :upscope]) 

# doesnt deal with subtyping
(defn- same-type? [t1 t2]
  (let [name1 (t1 :name)]
    (case name1 
      :function (and (= name1 (t2 :name)) (= (t1 :params) (t2 :params)) (= (t1 :ret) (t2 :ret)))
      (= (t1 :name) (t2 :name)))))

(defn- defprim [name]
  {:name name})

(defmacro- defprimitives [type-pairs]
  ;(map (fn [(key name)] ~(def ,name ,(defprim key))) (pairs type-pairs)))

(def Array :array)
(def Tuple :tuple)
(def Indexed :indexed)

(def Table :table)
(def Struct :struct)
(def Dict :dict)

(def Function :function)
(def CFunction :cfunction)

(defprimitives 
  {:string String
   :buffer Buffer
   :number Number
   :nil Nil
   :symbol Symbol
   :boolean Boolean
   :keyword Keyword
   :fiber Fiber
   :any Any})

(defn Function [&opt params ret]
  {:name :function
   :params params 
   :ret ret})
                
(defn- pp-type [typ]
  (defn- pp-function [typ]
    (let [params (typ :params)
          ret (typ :ret)]
      (string 
        "Function "
        (unless (nil? params)
          (let [positional (params :positional)
                optional (params :optional)
                variadic (params :variadic)]
            (string 
              (unless (nil? positional)
                (string/format "%p " (map pp-type positional))
                "")
              (unless (nil? optional)
                (string/format "&opt %p " (map pp-type optional))
                "")
              (unless (nil? variadic)
                (string/format "& %p" (pp-type variadic))
                "")))
          "")
        (unless (nil? ret)
          (string/format "-> %p" (pp-type ret))
          ""))))
          
  (defn- pp-t [typ]
    (case (typ :name)
      :string "String"
      :buffer "Buffer"
      :number "Number"
      :nil "Nil"
      :symbol "Symbol"
      :boolean "Boolean"
      :keyword "Keyword"
      :fiber "Fiber"
      :any "Any"
      :function (pp-function typ)))
  
  (pp-t typ))
  
  

(def- DEFAULT-RECORD
  @{:+ (Function {:variadic Number} Number)})

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
        (= (l :name) m) (set res l)
        (dictionary? m) (set res (m :type)))))
  res)

(defn- assert-type [declared inferred expr]
  (unless (same-type? declared inferred)
    (errorf "\n\tDeclared %s type in %p, but %p is a %s.\n" (pp-type declared) expr (last expr) (pp-type inferred))))
        
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
              (assert-type variadic-params (tc te var-arg) e)))))))

  (defn tc-do [te e]
    (var res nil)
    (each inner-expr (slice e 1)
      (set res (tc (create-type-env te) inner-expr)))
    res)

  (defn tc-def [te e]
    (let [lhs (get e 1)
          declared-type (extract-metadata (slice e 2 -1))
          inferred-type (tc te (last e))]
      (unless (nil? declared-type)
        (assert-type declared-type inferred-type e))
      (set-type te lhs inferred-type)
      inferred-type))

  (defn tc-set [te e]
    (let [lhs (get e 1)
          inferred-type (tc te (last e))]
      (set-type te lhs inferred-type)
      inferred-type))

  (defn tc-tuple [te e]
    (let [ef (macex e)]
      (case (keyword (first ef))
        :do (tc-do te ef)
        :def (tc-def te ef)
        :var (tc-def te ef)
        :set (tc-set te ef)
        (tc-application te ef))))
    
  (let [expr-type (type expr)]
    (case expr-type
      # :table (walk-dict f $f)
      # :struct (table/to-struct (walk-dict f $f))
      # :array (walk-ind f $f)
      :symbol (tc-symbol type-env (keyword expr))
      :tuple (tc-tuple type-env expr)
      (defprim expr-type))))

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
  
  (extract-metadata @[:a :b :number])
  (extract-metadata [:a :b {:type :number}])
  (extract-metadata [:a :b])

  # not quite right
  (pp-type (Function {:variadic Number} Number))

  (type-check 10)
  (type-check "string")
  (type-check @"buffer")
  (type-check (def x 10))
  (type-check (var x 10))
  (type-check (def x :string 10))
  (type-check (var x :string nil))
  (type-check (do 
                (var x nil)
                (set x "string")
                x))
  (type-check (do 
                (def x 10)
                @"yolo"))
  (type-check (do 
                (def x 10)
                (do 
                  (def x "string"))
                x))

  (type-check (+ 1 2))
  (type-check (+ 1 "yo"))

  (type-check '(1 2 3))

  (create-type-env)

  (def test-te (create-type-env))
  (tc test-te (def x 6))
  (tc test-te (def y x))

  (type-check (defn add [a b] (+ a b)))
  (type-check (if true true false)))
