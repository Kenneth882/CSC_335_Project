;This will be the syntax checker for TLS

;Design idea for Inductive defeniton

; So given the language of TLS we are supposed to create a syntax checker that checks if what the user put in as code
;has correct syntax which include but not limited to
;;     basic errors such as malformed cond and lambda expressions; (ii) detect when primitives are
;;     applied to the wrong number of arguments; and (iii) detect the presence of unbound variables.


;First we have to start off with all the primatives in TLS and store them in a list to assure that the syntax chekcer can refrence them
;; Globals

(define primitive-names
  '(car cdr cons null? pair? list? equal? atom? not
        + - * / = < > <= >= symbol? number? boolean?
        procedure? zero? add1 sub1 first second third))

;Now the question has to be asked if (cond, else, and , or, if ) need any checking?
;We know cond MUST end with an else so we have to keep that into consideration, else must also have
; some value come before it, as must and, and or, and if must only contain 2 possible outputs.
;In or TLS interpreter there were also some translations that we did from basic R5RS So we should also add that into the primitive-names pool.
; A simple way to maybe tackle the problem is to maybe have a cases function where our main body could refer to so once it finds the name of the primitive it then checks the
;amount of conditions it should have, so as an example atom? should only have 1 since its only checking one piece of information.
(define special-forms '(lambda cond if quote define and or))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers

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

(define (var? x env)
  (or (member? x env) (member? x primitive-names)))

(define (gathers errs lst env)
  (cond ((null? lst) errs)
        (else (let ((result (syntax-checker (car lst) env)))
                (if result
                    (gathers errs (cdr lst) env)
                    (gathers (cons (car lst) errs) (cdr lst) env))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Syntax Checker (using modulo dispatch)

(define (syntax-checker expr env)
  (cond
    ;; Base cases
    ((constant? expr) #t)
    ((symbol? expr) (var? expr env))
    ((and (pair? expr) (eq? (car expr) 'quote))
     (and (= (length expr) 2) #t))

    ;; Compound expressions
    ((pair? expr)
     (let ((op (car expr))
           (args (cdr expr)))
       (cond
         ((eq? op 'lambda) (check-lambda expr env))
         ((eq? op 'cond) (check-cond expr env))
         ((eq? op 'if) (check-if expr env))
         ((eq? op 'define) (check-define expr env))
         ((member? op primitive-names)
          (and (conditions op args)
               (null? (gathers '() args env))))
         (else (null? (gathers '() expr env))))))
    (else #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Arity Checking for Primitives

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
         (eq? name '+) (eq? name '-) (eq? name '*)
         (eq? name '/))
     (>= (length vals) 2))
    (else #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Form Checkers

(define (check-if expr env)
  (and (= (length expr) 4)
       (syntax-checker (second expr) env)
       (syntax-checker (third expr) env)
       (syntax-checker (fourth expr) env)))

(define (check-define expr env)
  (cond
    ;; define variable
    ((symbol? (second expr))
     (and (= (length expr) 3)
          (syntax-checker (third expr) env)))
    ;; define function
    ((and (pair? (second expr)) (symbol? (car (second expr))))
     (let* ((params (cdr (second expr)))
            (body (third expr))
            (new-env (append params env)))
       (and (not (duplicates? params))
            (syntax-checker body new-env))))
    (else #f)))

(define (check-lambda expr env)
  (and (= (length expr) 3)
       (let ((params (second expr))
             (body (third expr)))
         (and (list? params)
              (not (duplicates? params))
              (syntax-checker body (append params env))))))

(define (check-cond expr env)
  (define (clause-check lst)
    (cond
      ((null? lst) #t)
      ((not (pair? (car lst))) #f)
      ((eq? (car (car lst)) 'else)
       (and (null? (cdr lst)) 
            (null? (gathers '() (cdr (car lst)) env))))
      ((< (length (car lst)) 2) #f)
      (else
       (and (syntax-checker (caar lst) env)
            (null? (gathers '() (cdr (car lst)) env))
            (clause-check (cdr lst))))))
  (and (pair? expr)
       (> (length expr) 1)
       (clause-check (cdr expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Free Variable Detection (Optional Extension)

(define (element-lst? x lst)
  (cond ((null? lst) #f)
        ((equal? x (car lst)) #t)
        (else (element-lst? x (cdr lst)))))

(define (union-lst lst1 lst2)
  (cond ((null? lst1) lst2)
        ((element-lst? (car lst1) lst2) (union-lst (cdr lst1) lst2))
        (else (cons (car lst1) (union-lst (cdr lst1) lst2)))))

(define (free-vars expr bound)
  (cond
    ((symbol? expr)
     (if (element-lst? expr bound) '() (list expr)))
    ((constant? expr) '())
    ((and (pair? expr) (eq? (car expr) 'lambda))
     (let ((params (second expr))
           (body (third expr)))
       (free-vars body (append params bound))))
    ((and (pair? expr) (eq? (car expr) 'cond))
     (apply union-lst (map (lambda (clause)
                             (union-lst
                              (free-vars (car clause) bound)
                              (apply union-lst
                                     (map (lambda (x)
                                            (free-vars x bound))
                                          (cdr clause)))))
                           (cdr expr))))
    ((pair? expr)
     (union-lst (free-vars (car expr) bound)
                (free-vars (cdr expr) bound)))
    ((null? expr) '())
    (else '())))

(define (unbound-vars expr)
  (free-vars expr '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example Tests

;(syntax-checker '(lambda (x) (+ x 1)) '()) ; => #t
;(syntax-checker '(lambda (x x) (+ x 1)) '()) ; => #f
;(syntax-checker '(cond ((> x 0) #t) ((< x 0) #f) (else #f)) '()) ; => #t
;(syntax-checker '(if x 1) '()) ; => #f
;(syntax-checker '(+ 1) '()) ; => #f
;(unbound-vars '(lambda (x) (lambda (y) (+ x y z)))) ; => (z)
