#lang typed/racket
(require typed/rackunit)

; Full project implemented.

(define-type ExprC (U NumC IdC AppC Leq0C LamC StringC IfC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct Leq0C ([condition : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct IfC ([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct StringC ([val : String]) #:transparent)

(struct PlusC ([l : Real] [r : Real]))
(struct MinusC ([l : Real] [r : Real]))
(struct MultC ([l : Real] [r : Real]))
(struct DivC ([l : Real] [r : Real]))

(define-type Value (U Real Boolean String CloV PrimopV))
(struct PrimopV ([op : Symbol]))

(define-type Env (Listof Binding))
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define top-env (list (Binding 'true #t) (Binding 'false #f) (Binding '+ (PrimopV '+))))
(define extend-env cons)

(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (real? l) (real? r)) (+ l r)]
    [else
     (error 'num+ "one argument was not a number")]))


(define prims (make-immutable-hash
 (list (cons 'true #t)
       (cons 'false #f)
       (cons '+ +)
       (cons '- -))))

 (define (parse [sexp : Sexp]) : ExprC                                                                                
   (match sexp                                                  
          [(? string? val) (StringC val)]                                   
          [(? real? val) (NumC val)]                                        
          [(? symbol? val) (IdC val)]                                                                             
          [(list (? symbol? name) `= value) (parse value)]                                                        
          [(list `if if then else) (IfC (parse if) (parse then) (parse else))]                                   
          [(list `vars: vars ... `body: body) (desugar (cast vars (Listof Sexp)) body)]     
          [(list `proc (list (? symbol?) args ...) `go body) (LamC (cast args (Listof Symbol)) (parse body))]
          [(list (? symbol? op) a b) (AppC (IdC op) (list (parse a) (parse b)))]                              
          ))                                   
                                                                
 (define (desugar [vars : (Listof Sexp)] [body : Sexp]) : ExprC                 
   (AppC             
     (LamC (for/list [(var vars)] (cast (first (cast var (Listof Any))) Symbol)) (parse body)) 
     (for/list [(var vars)] (parse (cast (third (cast var (Listof Any))) Sexp)))
     ))                                                                                                 
                                                                                
; TODO: (check-equal? (desugar '{[z = {+ 9 14}] [y = 98]} {+ z y}) (AppC (LamC (list `z `y) {+ z y}) (list (NumC 5) (NumC 98)))) 


; Interp functions

(define (lookup [env : Env] [name : Symbol]) : Value
  (println env)
  (println name)
  (match env
    ;['() error]
    [(cons (Binding n val) r) (cond
                      [(equal? n name) val]
                      [else (lookup r name)])]))

(define (primop-eval [op : Symbol] [args : (Listof ExprC)] [env : Env]) : Value
  (define l (interp (first args) env))
  (define r (interp (second args) env))
  (cond
    [(and (equal? op '+) (real? l) (real? r)) (+ l r)]
    [else (error 'primop-eval "TODO")]))

(define (interp [exp : ExprC] [env : Env]) : Value
  ;(println exp)
  ;(println env)
  (match exp
    [(NumC n) n]
    [(IdC name) (lookup env name)]
    [(LamC a b) (CloV a b env)]
    [(AppC f a) (define fd (interp f env))
                  (match fd
                    [(PrimopV op) (primop-eval op a env)]
                    [(CloV params body env)
                      (define new-env ((inst map Binding ExprC Symbol)
                        (lambda (arg var) (Binding var (interp arg env))) a (CloV-params fd)))
                      (interp (CloV-body fd) ((inst foldl Binding Env) cons new-env (CloV-env fd)))])]))

;(interp (AppC (LamC '(a b) (IdC 'a)) (list (NumC 3) (NumC 10))) top-env)
;(interp (AppC (LamC '(a b) (IdC 'a)) (list (NumC 3) (NumC 10))) top-env)
;(check-equal? (parse '{vars: [z = {+ 9 14}] [y = 98] body: {+ z y}}) (AppC (LamC (list `z `y) (NumC 5)) (list (NumC 5) (NumC 98))))
(interp (parse '{vars: [z = {+ 2 13}] [y = 98] body: {+ z y}}) top-env)

; (define (top-interp [s : Sexp]) : String
;  (serialize (interp (parse s) top-env)))

(define (serializer [v : Value]) : String
  (match v
    [(? real? v) (~v v)]
    [(? boolean? v) (cond
                      [(false? v) "false"]
                      [else "true"])]
    [(? string? v) (~v v)]))

; (check-equal? (parse '{leq0? 1 3 {+ 1 2}}) (Leq0C (NumC 1) (NumC 3) (BinopC '+ (NumC 1) (NumC 2))))
; (check-equal? (parse '{leq0? -1 -2 {+ 1 2}}) (Leq0C (NumC -1) (NumC -2) (BinopC '+ (NumC 1) (NumC 2))))
; (check-equal? (parse '{+ x 14}) (BinopC '+ (IdC 'x) (NumC 14)))
; (check-equal? (parse '{double 3}) (AppC 'double (list (NumC 3))))
; (check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: 'leq0? (JYSS)"))
;            (lambda () (parse 'leq0?)))
; (check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: `(if then else) '() (JYSS)"))
;            (lambda () (parse '(leq0?))))
; (check-exn (regexp (regexp-quote "bad input, expected: Sexp result: '(/ 3 4 5) (JYSS)"))
;            (lambda () (parse '{/ 3 4 5})))
; (check-exn (regexp (regexp-quote "bad input, expected: Sexp result: '(/ + 5) (JYSS)"))
;            (lambda () (parse '{/ + 5})))
; (check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: 'fn (JYSS)"))
;            (lambda () (parse '{+ fn a})))

; (check-equal? (interp (BinopC '+ (NumC 4) (NumC 6)) '()) 10)
; (check-exn (regexp (regexp-quote "interp: cannot divide by zero (JYSS)"))
;            (lambda () (interp (BinopC '/ (NumC 2) (NumC 0)) '())))

; (check-= (top-interp (quote ((fn (minus-five x) (+ x 5))
;                              (fn (main init) (minus-five init))
;                              ))) 5 1e-3)
; (check-= (top-interp (quote ((fn (main init) (leq0? (* 3 1) 3 (+ 2 9)))))) 11 1e-3)
; (check-= (top-interp (quote ((fn (main init) (leq0? (- 0 1) 3 (+ 2 9)))))) 3 1e-3)
; (check-= (top-interp (quote ((fn (main init) (+ (f 13) (f 0))) (fn (f qq) (leq0? qq qq (+ qq 1)))))) 14 1e-3)

; (check-exn (regexp (regexp-quote "interp: number of arguments do not match (JYSS)"))
;            (lambda () (top-interp '((fn (f x) (+ x 2)) (fn (main) (f 3 4 5))))))
