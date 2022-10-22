#lang typed/racket
(require typed/rackunit)

; Full project implemented.

(define-type ExprC (U NumC IdC AppC Leq0C LamC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct Leq0C ([condition : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct FunDefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

(define-type Value (U Real Boolean String CloV))
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimopV ())
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define mt-env '())
(define extend-env cons)


(define symbol-to-op (make-immutable-hash
 (list (cons '+ +)
       (cons '- -)
       (cons '* *)
       (cons '/ /))))

; Interp functions

(define (lookup [env : Env] [name : Symbol]) : Value
  (match env
    ;['() error]
    [(cons (Binding n val) r) (cond
                      [(eq? n name) val]
                      [else (lookup r n)])]))

; consumes an ExprC and a list of function definitions and interprets the ExprC, outputting a Real
; (define (interp [exp : ExprC] [env : Env]) : Value
;   (match exp
;     [(IdC name) (lookup env name)]
;     [(LamC a b) (CloV a b env)]
;     [(AppC f a) (define argvals ((inst map Value ExprC) (lambda (x) (interp x env)) a))
;                 (define fd (interp f env))
;                   (match fd
;                     [(CloV params body env)
;                       (interp (CloV-body fd)
;                           (extend-env (Binding (CloV-params fd)
;                                           (interp a env))
;                                     (CloV-env fd)))])]))
(define (interp [exp : ExprC] [env : Env]) : Value
  (displayln exp)
  (displayln env) 
  (match exp
    [(NumC n) n]
    [(IdC name) (lookup env name)]
    [(LamC a b) (CloV a b env)]
    [(AppC f a) (define fd (interp f env))
                  (match fd
                    [(CloV params body env)
                      (define new-env ((inst map Binding ExprC Symbol) (lambda (arg var) (Binding var (interp arg env))) a (CloV-params fd)))
                      (interp (CloV-body fd) ((inst foldl Binding Env) cons new-env (CloV-env fd)))])]))

(interp (AppC (LamC '(a b) (IdC 'a)) (list (NumC 3) (NumC 10))) mt-env)
(cons (Binding 'a 111) (list (Binding 'b 10) (Binding 'z 2)))

; (define (top-interp [s : Sexp]) : String
;  (serialize (interp (parse s) top-env)))

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
