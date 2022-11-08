#lang typed/racket
(require typed/rackunit)

; Full project implemented.

(define-type ExprC (U NumC IdC AppC LamC StringC IfC RecC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct LamC ([args : (Listof TySymbol)] [body : ExprC]) #:transparent)
(struct IfC ([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct StringC ([val : String]) #:transparent)
(struct RecC ([fun : Symbol] [args : (Listof TySymbol)] [use : ExprC] [retT : Ty] [body : ExprC]) #:transparent)

(define-type Value (U Real Boolean String CloV PrimopV))
(struct PrimopV ([op : Symbol]))
(define-type Env (Listof Binding))
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct Binding ([name : Symbol] [val : (Boxof Value)]) #:transparent)
(define top-env (list (Binding 'true (box #t))
                      (Binding 'false (box #f))
                      (Binding '+ (box (PrimopV '+)))
                      (Binding '- (box (PrimopV '-)))
                      (Binding '* (box (PrimopV '*)))
                      (Binding '/ (box (PrimopV '/)))
                      (Binding 'num-eq? (box (PrimopV 'num-eq?)))
                      (Binding 'str-eq? (box (PrimopV 'str-eq?)))
                      (Binding 'substring (box (PrimopV 'substring)))
                      (Binding '<= (box (PrimopV '<=)))))

; Type Checking
(define-type Ty (U NumT StrT BoolT FunT))
(define-type TEnv (Listof BindingTy))
(struct BindingTy ([name : Symbol] [val : Ty]) #:transparent)
(struct NumT () #:transparent)
(struct StrT () #:transparent)
(struct BoolT () #:transparent)
(struct FunT ([args : (Listof Ty)] [ret : Ty]) #:transparent)
(struct TySymbol ([arg : Symbol] [type : Ty]) #:transparent)
(define base-tenv (list (BindingTy 'true (BoolT))
                        (BindingTy 'false (BoolT))
                        (BindingTy '+ (FunT (list (NumT) (NumT)) (NumT)))
                        (BindingTy '- (FunT (list (NumT) (NumT)) (NumT)))
                        (BindingTy '* (FunT (list (NumT) (NumT)) (NumT)))
                        (BindingTy '/ (FunT (list (NumT) (NumT)) (NumT)))
                        (BindingTy 'num-eq? (FunT (list (NumT) (NumT)) (BoolT)))
                        (BindingTy 'str-eq? (FunT (list (StrT) (StrT)) (BoolT)))
                        (BindingTy 'substring (FunT (list (StrT) (NumT) (NumT)) (StrT)))
                        (BindingTy '<= (FunT (list (NumT) (NumT)) (BoolT)))))

; Hash table for symbols that are not allowed as variables
(define reserved-ids (make-immutable-hash
 (list (cons 'if #f)
       (cons 'vars: #f)
       (cons 'body: #f)
       (cons 'proc #f)
       (cons 'go #f))))

; Combines parsing and evaluation
(define (top-interp [s : Sexp]) : String
 (serialize (interp (parse s) top-env)))

; Interprets an expression with an environment
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(StringC s) s]
    [(NumC n) n]
    [(IdC name) (unbox (lookup env name))]
    [(LamC a b) (CloV (map (lambda (x) (TySymbol-arg x)) a) b env)]
    [(IfC c t e) (cond
                      [(not (boolean? (interp c env))) (error 'interp "not a valid condition ~e (JYSS)" c)]
                      [(interp c env) (interp t env)]
                      [else (interp e env)])]
    [(AppC f a) (define fd (interp f env))
                  (match fd
                    [(PrimopV op) (primop-eval op ((inst map Value ExprC) (lambda (x) (interp x env)) a) env)]
                    [(CloV params body e)
                      (cond
                        [(not (equal? (length a) (length (CloV-params fd))))
                          (error 'interp "argument list and parameter list not equal size (JYSS)")])
                      (define new-env ((inst map Binding ExprC Symbol)
                                       (lambda (arg var) (Binding var (box (interp arg env)))) a params))
                      (interp body (append new-env e))]
                    [other (error 'interp "bad syntax ~e (JYSS)" exp)])]
    [(RecC f a u r b) (define dummy-env (cons (Binding f (box -1)) env))
                      (set-box! (lookup dummy-env f) (CloV (map (lambda (x) (TySymbol-arg x)) a) u dummy-env))
                      (interp b dummy-env)]))

; Parses an s-expression
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? string? val) (StringC val)]
    [(? real? val) (NumC val)]
    [(? symbol? val) (cond
                       [(not (hash-has-key? reserved-ids val)) (IdC val)]
                       [else (error 'parse "not a valid argument ~e (JYSS)" val)])]
    [(list (? symbol? name) `= value) (parse value)]
    [(list `if if then else) (IfC (parse if) (parse then) (parse else))]
    ;[(list `vars: vars ... `body: body) (desugar (cast vars (Listof Sexp)) body)] 
    ;[(list `proc (list (? symbol? s) args ...) `go body)
    ;      (cond [(false? (check-duplicates (cons s args))) (LamC (cast (cons s args) (Listof Symbol)) (parse body))]
    ;            [else (error 'parse "two or more parameters with same identifier ~e (JYSS)" args)])]
    [(list 'proc (list (list (? symbol? s) ': ty) ...) 'go body)
       (cond [(false? (check-duplicates s))
                (define types ((inst map Ty Sexp) (lambda (t) (parse-type t)) (cast ty (Listof Sexp))))
                (LamC ((inst map TySymbol Symbol Ty)
                       (lambda (arg type) (TySymbol arg type)) (cast s (Listof Symbol)) types) (parse body))]
             [else (error 'parse "two or more parameters with same identifier ~e (JYSS)" s)])]
      ; (println s) (println ty) (println body)(NumC 1)]
    [(list `proc (list) `go body) (LamC (list) (parse body))]
    [(list (? symbol? op) a b) (AppC (IdC op) (list (parse a) (parse b)))]
    [(list a b ...) (AppC (parse a) ((inst map ExprC Sexp) parse b))]))

(define (parse-type [sexp : Sexp]) : Ty
  (match sexp
    ['num (NumT)]
    ['str (StrT)]
    ['bool (BoolT)]
    [(list tys ... '-> ret) (FunT ((inst map Ty Sexp) (lambda (x) (parse-type x)) (cast tys (Listof Sexp))) (parse-type ret))]
    [other (error 'parse-type "bad type ~e (JYSS)" sexp)]))

(check-equal? (parse '{proc {[z : num] [y : num]} go {+ z y}}) (LamC (list (TySymbol 'z (NumT)) (TySymbol 'y (NumT))) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))))

; Desugars local variable definitions into ExprC
;(define (desugar [vars : (Listof Sexp)] [body : Sexp]) : ExprC
;  (define args (for/list ([var vars]) : (Listof Symbol) (cast (first (cast var (Listof Any))) Symbol)))
;  (for/or ([arg args]) : Boolean #:break (not (hash-has-key? reserved-ids arg))
;    (error 'parse "not valid syntax ~e (JYSS)" args))
;  (cond
;    [(false? (check-duplicates args))
;      (AppC
  ;     (LamC args (parse body))
;       (for/list [(var vars)] (parse (cast (third (cast var (Listof Any))) Sexp))))]
 ;   [else (error 'desugar "bad syntax for arguments ~e (JYSS)" vars)]))

; Looksup a symbol's value in a given environment
(define (lookup [env : Env] [name : Symbol]) : (Boxof Value)
  (match env
    ['() (error 'lookup "name not found: ~e (JYSS)" name)]
    [(cons (Binding n val) r) (cond
                      [(equal? n name) val]
                      [else (lookup r name)])]))

; Looksup a symbol's type in a given type environment
(define (lookup-type [env : TEnv] [name : Symbol]) : Ty
  (match env
    ['() (error 'lookup "name not found: ~e (JYSS)" name)]
    [(cons (BindingTy n val) r) (cond
                      [(equal? n name) val]
                      [else (lookup-type r name)])]))

; Helper function to evaluate primitive operators with a given environment, returning a value
(define (primop-eval [op : Symbol] [args : (Listof Value)] [env : Env]) : Value
  (match op
    ['true #t]
    ['false #f]
    ['num-eq? (cond
              [(equal? (length args) 2) (equal? (first args) (second args))]
              [else (error 'primop-eval "wrong number of arguments: ~e (JYSS)" args)])]
    ['str-eq? (cond
              [(equal? (length args) 2) (equal? (first args) (second args))]
              [else (error 'primop-eval "wrong number of arguments: ~e (JYSS)" args)])]
    ['substring (define str (first args))
                (define start (second args))
                (define end (third args))
                (cond
                  [(and (string? str) (exact-nonnegative-integer? start) (exact-nonnegative-integer? end))
                     (substring str start end)]
                  [else (error 'primop-eval "type mismatch in arguments ~e ~e ~e" str start end)])]
    [op
      (define l (first args))
      (define r (second args))
      (cond
        [(not (equal? (length args) 2)) (error 'primop-eval "wrong number of arguments ~e (JYSS)" args)]
        [(and (equal? op '+) (real? l) (real? r)) (+ l r)]
        [(and (equal? op '-) (real? l) (real? r)) (- l r)]
        [(and (equal? op '*) (real? l) (real? r)) (* l r)]
        [(and (equal? op '/) (real? l) (real? r)) (cond
                                                    [(not (equal? 0 r)) (/ l r)]
                                                    [else (error 'primop-eval "divide by zero (JYSS)")])]
        [(and (equal? op '<=) (real? l) (real? r)) (<= l r)]
        [else (error 'primop-eval "invalid operator/arguments ~e (JYSS)" op)])]))

; Accept a JYSS5 value, and returns a string
(define (serialize [v : Value]) : String
  (match v
    [(? real? v) (~v v)]
    [(? boolean? v) (cond
                      [(false? v) "false"]
                      [else "true"])]
    [(? string? v) (~v v)]
    [(? CloV? v) "#<procedure>"]
    [(? PrimopV? v) "#<primop>"]))

; Accepts a ExprC and a TEnv then evaluates the type of the ExprC using the type environment  
(define (type-check [expr : ExprC] [tenv : TEnv]) : Ty
  (match expr
    [(NumC n) (NumT)]
    [(IdC s) (lookup-type tenv s)]
    [(IfC c t e) (cond
                   [(not (equal? (BoolT) (type-check c tenv)))
                    (error 'type-check "condition is not a boolean ~e (JYSS)" c)]
                   [(not (equal? (type-check t tenv) (type-check e tenv)))
                    (error 'type-check "then and else clauses are different types ~e ~e" t e)]
                   [else (type-check t tenv)])]
    [(LamC a b) (define new-tenv ((inst map BindingTy TySymbol)
                                  (lambda (bt) (BindingTy (TySymbol-arg bt) (TySymbol-type bt))) a))
                (FunT (map (lambda (x) (TySymbol-type x)) a) (type-check b (append new-tenv tenv)))]
    [(AppC f a) (define ft (type-check f tenv))
                (define at ((inst map Ty ExprC) (lambda (arg) (type-check arg tenv)) a))
                  (cond
                    [(not (FunT? ft))
                     (error 'type-check "not a function ~e" f)]
                    [(not (equal? (FunT-args ft) at))
                     (error 'type-check  "app arg mismatch ~e" a)]
                    [else (FunT-ret ft)])]
    [(RecC f a u r b) (define new-tenv (cons (BindingTy f (FunT (map (lambda (x) (TySymbol-type x)) a) r)) tenv))
                      (define body-tenv (append ((inst map BindingTy TySymbol)
                                           (lambda (bt) (BindingTy (TySymbol-arg bt) (TySymbol-type bt))) a) new-tenv))
                      (cond
                        [(not (equal? r (type-check b body-tenv)))
                         (error 'type-check "body return type not correct ~e" b)]
                        [else (type-check u new-tenv)])]))

(check-exn (regexp (regexp-quote "primop-eval: user-error '(\"1234\")"))
           (lambda () (primop-eval 'error (list "1234") top-env)))
(check-equal? (parse '"sample") (StringC "sample"))
(check-equal? (parse '{f = 2}) (NumC 2))
(check-equal? (parse '{if x 10 1}) (IfC (IdC 'x) (NumC 10) (NumC 1)))
(check-equal? (parse '{proc {[z : int] [y : int]} go {+ z y}}) (LamC (list (TySymbol 'z (NumT)) (TySymbol 'y (NumT))) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))))
(check-equal? (parse '{{g} 15}) (AppC (AppC (IdC 'g) '()) (list (NumC 15))))
(check-exn (regexp (regexp-quote "parse: not valid syntax '(go) (JYSS)"))
           (lambda () (parse '(vars: (go = "") body: "World"))))
(check-exn (regexp (regexp-quote "parse: not a valid argument 'if (JYSS)"))
           (lambda () (parse '{+ if 4})))
(check-exn (regexp (regexp-quote "two or more parameters with same identifier '(x) (JYSS)"))
           (lambda () (parse '{proc {x x} go 3})))
(check-exn (regexp (regexp-quote "desugar: bad syntax for arguments '((z = (proc () go 3)) (z = 9)) (JYSS)"))
           (lambda () (parse '(vars: (z = (proc () go 3)) (z = 9) body: (z)))))
(check-equal? (top-interp (quote (if true + -))) "#<primop>")
(check-equal? (top-interp (quote (if false + -))) "#<primop>")
(check-equal? (top-interp (quote (if (<= 4 3) 29387 true))) "true")
(check-exn (regexp (regexp-quote "interp: not a valid condition (AppC (IdC '+) (list (NumC 4) (NumC 3))) (JYSS)"))
           (lambda () (top-interp '(if (+ 4 3) 7 8))))
(check-exn (regexp (regexp-quote "primop-eval: divide by zero (JYSS)"))
           (lambda () (top-interp '(/ 1 (+ -3 3)))))
(check-exn (regexp (regexp-quote "primop-eval: divide by zero (JYSS)"))
           (lambda () (top-interp '(/ 1 (+ -3 3)))))
(check-exn (regexp (regexp-quote "interp: bad syntax (AppC (NumC 3) (list (NumC 4) (NumC 5))) (JYSS)"))
           (lambda () (top-interp '(3 4 5))))
(check-exn (regexp (regexp-quote "primop-eval: user-error '(\"1234\")"))
           (lambda () (top-interp '(+ 4 (error "1234")))))
(check-equal? (primop-eval '- (list 1 2) top-env) -1)
(check-equal? (primop-eval '* (list 1 2) top-env) 2)
(check-equal? (primop-eval '/ (list 4 2) top-env) 2)
(check-equal? (primop-eval 'true '() top-env) #t)
(check-equal? (primop-eval 'false '() top-env) #f)
(check-equal? (primop-eval 'equal? (list 3 3) top-env) #t)
(check-equal? (primop-eval 'equal? (list 3 4) top-env) #f)
(check-exn (regexp (regexp-quote "lookup: name not found: 'f (JYSS)"))
           (lambda () (lookup '() 'f)))
(check-exn (regexp (regexp-quote "primop-eval: wrong number of arguments '(1 2 3) (JYSS)"))
           (lambda () (primop-eval '- (list 1 2 3) top-env)))
(check-exn (regexp (regexp-quote "primop-eval: invalid operator/arguments '! (JYSS)"))
           (lambda () (primop-eval '! (list 1 2) top-env)))
(check-exn (regexp (regexp-quote "primop-eval: wrong number of arguments: '(1 \"f\" 4) (JYSS)"))
           (lambda () (primop-eval 'equal? (list 1 "f" 4) top-env)))
(check-equal? (top-interp '{vars: [z = {+ 2 13}] [y = 98] body: {+ z y}}) "113")
(check-equal? (top-interp '{proc () go 9}) "#<procedure>")
(check-exn (regexp (regexp-quote "interp: argument list and parameter list not equal size (JYSS)"))
           (lambda () (top-interp '((proc () go 9) 17))))
(check-equal? (serialize #f) "false")
(check-equal? (serialize #t) "true")
(check-equal? (serialize "random") "\"random\"")
(check-equal? (serialize (CloV  '() (NumC 4) '())) "#<procedure>")
(check-equal? (serialize (PrimopV '+)) "#<primop>")