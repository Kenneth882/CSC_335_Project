;This will be the syntax checker for TLS

;Design idea for Inductive defeniton

; So given the language of TLS we are supposed to create a syntax checker that checks if what the user put in as code
;has correct syntax which include but not limited to
;;     basic errors such as malformed cond and lambda expressions; (ii) detect when primitives are
;;     applied to the wrong number of arguments; and (iii) detect the presence of unbound variables.

;Loading

;In class we went over the specifications of a "Module Dispatch" and how it should work in the TLS system with the syntax checker
;this will serve as out dispatch where we 


;change this to the 1.1 file name
(load "Choudhury.Juarez.Romero.1.1.scm")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (constant? x)
  (or (number? x) (boolean? x) (string? x) (char? x)))

(define (member? x lst)
  (cond ((null? lst) #f)
        ((eq? x (car lst)) #t)
        (else (member? x (cdr lst)))))

(define (duplicates? lst)
  (cond ((null? lst) #f)
        ((member? (car lst) (cdr lst)) #t)
        (else (duplicates? (cdr lst)))))

;here we use x as our varible the env as the enviorment and the tls as our datatype lookup
;so in this case it returns true if x is in out current lexical enviorment or built in primitive
(define (var? x env tls)
  (or (member? x env) (member? x (tls 'primitives))))

;This serves as our error function which stores the errors in our syntax, lst is the expressions needing to be checked
;env is the enviorment and the tls is out module refered to. We use this to recursivly check all our sub-expressions
(define (gathers errs lst env tls)
  (cond ((null? lst) errs)
        (else (let ((result (syntax-checker (car lst) env tls)))
                (if result
                    (gathers errs (cdr lst) env tls)
                    (gathers (cons (car lst) errs) (cdr lst) env tls))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Syntax Checker
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Our main function syntax-checker consists of of the expr which is our current value,
;the enviorment and module dispatch

;How does this work??
;This is mainly used to check if an epxr is valid under TLS rules and simply retuns a #t or a #f based on it.
;at first it simply checks the constants and varibles and then if the expr is a special form it is in charge of
;sending that expr into its check function which then checks if that special form is valid.
(define (syntax-checker expr env tls)
  (cond
    ((constant? expr) #t)
    ((symbol? expr) (var? expr env tls))
    ((and (pair? expr) (eq? (car expr) 'quote))
     (and (= (length expr) 2) #t))
    ((pair? expr)
     (let ((op (car expr)) 
           (args (cdr expr)))
       (cond
         ((eq? op 'lambda) (check-lambda expr env tls))
         ((eq? op 'cond)   (check-cond expr env tls))
         ((eq? op 'if)     (check-if expr env tls))
         ((and (pair? op) (eq? (car op) 'lambda))
         ;lambda-arity checker, first it checks above if the lambda is valid
          ;then it checks out if ate arguments have the correct value
          ;then we just ask if the arguments are valid expressions
          (and (check-lambda op env tls)
               (= (length args) (length (second op)))
               (null? (gathers '() args env tls))))
         ((member? op (tls 'primitives))
          (and (conditions op args)
               (null? (gathers '() args env tls))))
         (else (null? (gathers '() expr env tls))))))
    (else #f)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Arity Checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Simple checker for condtions and correct Arity.
(define (conditions name vals)
  (cond
    ((or (eq? name 'car) (eq? name 'cdr) (eq? name 'first)
         (eq? name 'second) (eq? name 'third)
         (eq? name 'pair?) (eq? name 'atom?) (eq? name 'symbol?)
         (eq? name 'number?) (eq? name 'boolean?) (eq? name 'zero?)
         (eq? name 'add1) (eq? name 'sub1))
     (= (length vals) 1))
    ((eq? name 'cons) (= (length vals) 2))
    ((or (eq? name 'equal?) (eq? name '=)
         (eq? name '<) (eq? name '>) (eq? name '<=) (eq? name '>=)
         (eq? name '+) (eq? name '-) (eq? name '*) (eq? name '/))
     (>= (length vals) 2))
    (else #f)))


;; Check if lambda expression is well-formed
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Form Checkers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;This is based around the strcuture of (if test then else): so we need len 4.
;we test that all the parts  follow the Tls syntax so that an if without an else would be unvalid
; or a if with too many parts would also be unvalid, so our if has to fufill the requirments

(define (check-if expr env tls)
  (and (= (length expr) 4)
       (syntax-checker (second expr) env tls)
       (syntax-checker (third expr) env tls)
       (syntax-checker (cadddr expr) env tls)))

;(syntax-checker '(if (> x 0) 1 2) '(x) tls)   ; → #t
;(syntax-checker '(if x 1) '(x) tls)           ; → #f (missing else)
;(syntax-checker '(if x 1 2 3) '(x) tls)       ; → #f (too many parts)


;Checks for lambda where the form must be in (lambda(parameters) body) hence the length 3
; we ensure that our parameters must be a list of symbols, and that we have no duplicates as well as
;our body being valid an enviorment extendned with those parameters
(define (check-lambda expr env tls)
  (cond
    ((not (= (length expr) 3)) 
     #f)
    ((not (list? (second expr))) 
     #f)
    ((duplicates? (second expr)) 
     #f)
    (else
     (let* ((params (second expr))
            (body   (third expr))
            (new-env (append params env))) 
       (syntax-checker body new-env tls)))))

;(syntax-checker '(lambda (x) (+ x 1)) '() tls)         ; → #t
;(syntax-checker '(lambda (x x) (+ x 1)) '() tls)       ; → #f
;(syntax-checker '(lambda x (+ x 1)) '() tls)           ; → #f (params not a list)

;This is our check-cond: in each call we test that each clause MUST be a list
; and that the last and only last part has to  be an else
(define (check-cond expr env tls)
  (define (clause-check lst)
    (cond
      ((null? lst) #t)
      ((not (list? (car lst))) #f)
      ((eq? (car (car lst)) 'else)
       (and (null? (cdr lst)) 
            (null? (gathers '() (cdr (car lst)) env tls))))
      ((< (length (car lst)) 2) #f)
      (else
       (and (syntax-checker (caar lst) env tls)
            (null? (gathers '() (cdr (car lst)) env tls))
            (clause-check (cdr lst))))))
  (and (list? expr)
       (> (length expr) 1)
       (clause-check (cdr expr))))

;Test these Bellow after tls-module Defenition!

;(syntax-checker '(cond ((> x 0) 'pos) (else 'zero)) '(x) tls) ; → #t
;(syntax-checker '(cond ((> x 0)) (else 'ok)) '(x) tls)        ; → #f (missing result)
;(syntax-checker '(cond ((> x 0) 1) ((< x 0) 2) (else)) '(x) tls) ; → #f (empty else)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Free Variable Detection
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; This function checks whether a given element x appears in the list last.
;; If the list is empty, then x is not found.
; we keep on doing this until x is found or not found.
(define (element-lst? x lst)
  (cond ((null? lst) #f)
        ((equal? x (car lst)) #t)
        (else (element-lst? x (cdr lst)))))

; This function returns the union of two lists, preserving order and avoiding duplicates.
; How it works:
; If the first list is empty, the union is simply the second list.
; If the first element of lst1 already appears in lst2, skip it and continue.
; Otherwise, include the first element of lst1 in the result and continue.
(define (union-lst lst1 lst2)
  (cond ((null? lst1) lst2)
        ((element-lst? (car lst1) lst2) (union-lst (cdr lst1) lst2))
        (else (cons (car lst1) (union-lst (cdr lst1) lst2)))))


;unbound-vars* takes two arguments—an expression and a list of names that are already considered
;bound—and returns a list of all symbols in the expression that do not appear in that bound list. It
;proceeds by examining the expression’s structure
(define (unbound-vars* expr bound)
  (cond
    ((symbol? expr)
     (if (element-lst? expr bound) '() (list expr)))
    ((constant? expr) '())
    ((and (pair? expr) (eq? (car expr) 'lambda))
     (let ((params (second expr))
           (body (third expr)))
       (unbound-vars* body (append params bound))))
    ((and (pair? expr) (eq? (car expr) 'cond))
     (apply union-lst (map (lambda (clause)
                             (union-lst
                              (unbound-vars* (car clause) bound)
                              (apply union-lst
                                     (map (lambda (x)
                                            (unbound-vars* x bound))
                                          (cdr clause)))))
                           (cdr expr))))
    ((pair? expr)
     (union-lst (unbound-vars* (car expr) bound)
                (unbound-vars* (cdr expr) bound)))
    ((null? expr) '())
    (else '())))

(define (unbound-vars expr)
  (unbound-vars* expr '()))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example Tests



(syntax-checker '(lambda (x) (+ x 1) ) '() tls) ; => #t
(syntax-checker '(+ 1) '() tls)               ; => #f
(unbound-vars '(lambda (x) (lambda (y) (+ x y z)))) ; => (z)

(syntax-checker '(cond ((> x 0) 'pos) (else 'zero)) '(x) tls) ; → #t
(syntax-checker '(cond ((> x 0)) (else 'ok)) '(x) tls)        ; → #f (missing result)
(syntax-checker '(cond ((> x 0) 1) ((< x 0) 2) (else)) '(x) tls) ; → #f (empty else)

(define lam‐too‐few '((lambda (a b) (+ a b)) 7))
(syntax-checker lam‐too‐few '() tls)

(define lam‐ok '((lambda (a b) (+ a b)) 7 8))
(syntax-checker lam‐ok '() tls)

(define lam‐nested‐ok '(((lambda (p) (lambda (q) (+ p q))) 1) 2))
(syntax-checker lam‐nested‐ok '() tls) 

; Valid nested
(syntax-checker '((lambda (x) (if x 1 2)) #t) '() tls) ; → #t
(syntax-checker '(cond ((= x 0) 0) ((> x 0) 1) (else -1)) '(x) tls) ; → #t

; Invalid nested
(syntax-checker '((lambda (x) (if x 1)) #t) '() tls)    ; → #f (missing else)
(syntax-checker '(cond ((= x 0)) ((> x 0) 1) (else -1)) '(x) tls) ; → #f (missing result)

(syntax-checker '() '() tls)                    ; → #f (invalid expr)
(syntax-checker '(()) '() tls)                  ; → #f (invalid expr)

; Malformed special forms
(syntax-checker '(lambda) '() tls)              ; → #f (malformed)
(syntax-checker '(if) '() tls)                  ; → #f (malformed)
(syntax-checker '(cond) '() tls)                ; → #f (malformed)
