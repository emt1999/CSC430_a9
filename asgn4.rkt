#lang typed/racket
(require typed/rackunit)

; Full project implemented.

(define-type ExprC (U NumC BinopC IdC AppC Leq0C))
(struct BinopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : Symbol] [arg : (Listof ExprC)]) #:transparent)
(struct Leq0C ([condition : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct FunDefC ([name : Symbol] [arg : (Listof Symbol)] [body : ExprC]) #:transparent)

(define symbol-to-op (make-immutable-hash
 (list (cons '+ +)
       (cons '- -)
       (cons '* *)
       (cons '/ /))))

(define invalid-fns (make-immutable-hash
 (list (cons 'leq0? #f)
       (cons 'fn #f)
       (cons '+ #f)
       (cons '- #f)
       (cons '* #f)
       (cons '/ #f))))

; Parse functions

; consumes a s-expression and outputs a ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(cons 'leq0? rest)
     (match rest
       [(list condition then else) (Leq0C (parse condition) (parse then) (parse else))]
       [err (error `parse "bad input, expected: Sexp result: `(if then else) ~e (JYSS)" err)])]
    [(? real? s) (NumC s)]
    [(? symbol? s)
     (cond
       [(not (hash-has-key? invalid-fns s)) (IdC s)]
       [else (error `parse "bad input, expected: Sexp result: ~e (JYSS)" s)])]
    [(list (? symbol? op) l r) #:when (and (hash-has-key? symbol-to-op op) (not (hash-has-key? symbol-to-op l))
                                           (not (hash-has-key? symbol-to-op r)))
                               (BinopC op (parse l) (parse r))]
    [(list (? symbol? s) a ...) #:when (not (hash-has-key? symbol-to-op s))
                                (AppC s (map parse a))]
    [err
     (error 'parse "bad input, expected: Sexp result: ~e (JYSS)" err)]))

; consumes an s-expression that is a function definition and outputs a FunDefC
(define (parse-fundef [s : Sexp]) : FunDefC
  (match s
    [(list 'fn (list (? symbol? name)) body)
     #:when (and (not (hash-has-key? symbol-to-op name)))
                                                             (FunDefC name '() (parse body))]
    [(list 'fn (list (? symbol? name) args ...) body)
     #:when (and (not (hash-has-key? symbol-to-op name)) (not (for/and ([i args]) : Boolean
                                                                (hash-has-key? symbol-to-op i))))
                                                             (FunDefC name (cast args (Listof Symbol)) (parse body))]
    
    [other (error 'parse-fundef "JYSS: bad input, expected: Sexp result: ~e (JYSS)" other)]))

; consumes an s-expression with the program body and produces a list of function definitions
(define (parse-prog [s : Sexp]) : (Listof FunDefC)
  (match s
    ['() '()]
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]))

; Interp functions

; consumes an ExprC and a list of function definitions and interprets the ExprC, outputting a Real
(define (interp [exp : ExprC] [funs : (Listof FunDefC)]) : Real
  (match exp
    [(NumC n) n]
    [(Leq0C condition then else)
     (cond
          [(<= (interp condition funs) 0) (interp then funs)]
          [else (interp else funs)])]
    [(AppC f a) (define fd (get-fundef f funs))
                (cond
                  [(eq? (length (FunDefC-arg fd)) (length a))
                   (interp (subst-args (for/list ([i a]) (NumC (interp i funs)))
                               (FunDefC-arg fd)
                               (FunDefC-body fd))
                        funs)]
                  [else (error 'interp "number of arguments do not match (JYSS)")])]
    [(IdC `init) 0]
    [(BinopC op l r) #:when (and (eq? op '/) (eq? (interp r funs) 0)) (error 'interp "cannot divide by zero (JYSS)")]
    [(BinopC op l r) ((hash-ref symbol-to-op op) (interp l funs) (interp r funs))]))  

; consumes a list of function definitions
(define (interp-fns [funs : (Listof FunDefC)]) : Real
  (interp (FunDefC-body (get-fundef 'main funs)) funs))

(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

; helper function that takes in a symbol and a list of function definition and matches it to a
; function definiton in the input list then outputs a FunDefC
(define (get-fundef [n : Symbol] [fds : (Listof FunDefC)]) : FunDefC
    (cond
      [(empty? fds)
       (error 'get-fundef "reference to undefined function (JYSS)")]
      [(cons? fds)
       (cond
         [(equal? n (FunDefC-name (first fds))) (first fds)]
         [else (get-fundef n (rest fds))])]))

; helper function that takes in a ExprC (what to replace the name with), a symbol
; (the name to perform substitution on), and in which ExprC to do it and outputs the substituted ExprC
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in
    [(NumC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (for/list ([i a]) (subst what for i)))]
    [(BinopC op l r) (BinopC op
                             (subst what for l)
                             (subst what for r))]
    [(Leq0C condition then else) (Leq0C (subst what for condition)
                                        (subst what for then)
                                        (subst what for else))]))

; consumes a list of ExprC, a list of Symbols, and an ExprC, then calls subst on each arg
; in order to substitute the body producing an ExprC
(define (subst-args [what : (Listof ExprC)] [for : (Listof Symbol)] [in : ExprC]) : ExprC
  (match what
    ['() in]
    [(cons f r) (subst-args r (rest for) (subst f (first for) in))]))

; Test Cases

(check-equal? (parse '{leq0? 1 3 {+ 1 2}}) (Leq0C (NumC 1) (NumC 3) (BinopC '+ (NumC 1) (NumC 2))))
(check-equal? (parse '{leq0? -1 -2 {+ 1 2}}) (Leq0C (NumC -1) (NumC -2) (BinopC '+ (NumC 1) (NumC 2))))
(check-equal? (parse '{+ x 14}) (BinopC '+ (IdC 'x) (NumC 14)))
(check-equal? (parse '{double 3}) (AppC 'double (list (NumC 3))))
(check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: 'leq0? (JYSS)"))
           (lambda () (parse 'leq0?)))
(check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: `(if then else) '() (JYSS)"))
           (lambda () (parse '(leq0?))))
(check-exn (regexp (regexp-quote "bad input, expected: Sexp result: '(/ 3 4 5) (JYSS)"))
           (lambda () (parse '{/ 3 4 5})))
(check-exn (regexp (regexp-quote "bad input, expected: Sexp result: '(/ + 5) (JYSS)"))
           (lambda () (parse '{/ + 5})))
(check-exn (regexp (regexp-quote "parse: bad input, expected: Sexp result: 'fn (JYSS)"))
           (lambda () (parse '{+ fn a})))

(check-equal? (parse-fundef '{fn {f x} {+ 2 14}}) (FunDefC 'f (list 'x) (BinopC '+ (NumC 2) (NumC 14))))
(check-exn (regexp (regexp-quote "bad input, expected: Sexp result: '(fn (+ x) 13) (JYSS)"))
           (lambda () (parse-fundef '(fn (+ x) 13))))

(check-equal? (parse-prog '{{fn {f x} {+ 2 14}}
                           {fn {main init} {+ 2 2}}}) (list
                                                       (FunDefC 'f (list 'x) (BinopC '+ (NumC 2) (NumC 14)))
                                                       (FunDefC 'main (list 'init) (BinopC '+ (NumC 2) (NumC 2)))))

(check-equal? (interp (BinopC '+ (NumC 4) (NumC 6)) '()) 10)
(check-exn (regexp (regexp-quote "interp: cannot divide by zero (JYSS)"))
           (lambda () (interp (BinopC '/ (NumC 2) (NumC 0)) '())))

(check-equal? (interp-fns
       (parse-prog '{{fn {f x} {+ x 14}}
                     {fn {main init} {f 2}}}))
      16)

(check-= (top-interp (quote ((fn (minus-five x) (+ x 5))
                             (fn (main init) (minus-five init))
                             ))) 5 1e-3)
(check-= (top-interp (quote ((fn (main init) (leq0? (* 3 1) 3 (+ 2 9)))))) 11 1e-3)
(check-= (top-interp (quote ((fn (main init) (leq0? (- 0 1) 3 (+ 2 9)))))) 3 1e-3)
(check-= (top-interp (quote ((fn (main init) (+ (f 13) (f 0))) (fn (f qq) (leq0? qq qq (+ qq 1)))))) 14 1e-3)

(check-exn (regexp (regexp-quote "get-fundef: reference to undefined function (JYSS)"))
           (lambda () (get-fundef 'n '())))
(check-equal? (get-fundef 'blah (list (FunDefC 'blah (list 'x) (NumC 4)))) (FunDefC 'blah (list 'x) (NumC 4)))

(check-exn (regexp (regexp-quote "interp: number of arguments do not match (JYSS)"))
           (lambda () (top-interp '((fn (f x) (+ x 2)) (fn (main) (f 3 4 5))))))

(check-equal? (subst-args (list (NumC 1) (NumC 2)) (list 'z 'v) (AppC 'f (list (IdC 'z) (IdC 'v))))
              (AppC 'f (list (NumC 1) (NumC 2))))
(check-equal? (subst (NumC 2) `x (BinopC `+ (NumC 2) (IdC `y))) (BinopC `+ (NumC 2) (IdC `y)))
