
;this is refering to our filed called Project.rkt which contains our tls interpreter along with built in TLS primitives
(load "Project.rkt")

;This will be the syntax checker for TLS

;Design idea for Inductive defeniton

; So given the language of TLS we are supposed to create a syntax checker that checks if what the user put in as code
;has correct syntax which include but not limited to
;;     basic errors such as malformed cond and lambda expressions; (ii) detect when primitives are
;;     applied to the wrong number of arguments; and (iii) detect the presence of unbound variables.



;First we have to start off with all the primatives in TLS and store them in a list to assure that the syntax chekcer can refrence them

(define primitive-names
  '(car cdr cons null? pair? list? equal? atom? not
        + - * / = < > <= >= symbol? number? boolean? procedure? zero? add1 sub1 first second third))

;I think this is not needed so we should probably forget about the special-forms
;--------------------------------------------------------------------------------------------------
;Now the question has to be asked if (cond, else, and , or, if ) need any checking?
;We know cond MUST end with an else so we have to keep that into consideration, else must also have
; some value come before it, as must and, and or, and if must only contain 2 possible outputs.
;In or TLS interpreter there were also some translations that we did from basic R5RS So we should also add that into the primitive-names pool.
; A simple way to maybe tackle the problem is to maybe have a cases function where our main body could refer to so once it finds the name of the primitive it then checks the
;amount of conditions it should have, so as an example atom? should only have 1 since its only checking one piece of information.
;-------------------------------------------------------------------------------------------------
(define special-forms '(lambda cond if quote and or))


;This is all the condtions that are needed to check if the syntax is valid or not
; name is the primitive that is being checked and vals is the supposed vals that makes it a correct syntax

(define (conditions name vals)
  (cond
    ((or (eq? name 'car) (eq? name 'first)) (= (length vals) 1))
    ((eq? name 'cdr) (= (length vals) 1))
    ((eq? name 'cons) (= (length vals) 2))
    ((eq? name 'pair?) (= (length vals) 1))
    ((eq? name 'equal?) (= (length vals) 2))
    ((eq? name 'atom?) (= (length vals) 1))
    ((eq? name 'symbol?) (= (length vals) 1))
    ((eq? name 'number?) (= (length vals) 1))
    ((eq? name 'boolean?) (= (length vals) 1))
    ((eq? name 'zero?) (= (length vals) 1))
    ((eq? name 'add1) (= (length vals) 1))
    ((eq? name 'sub1) (= (length vals) 1))
    ((eq? name 'second) (= (length vals) 1))
    ((eq? name 'third) (= (length vals) 1))
    ((or (eq? name '+) (eq? name '-) (eq? name '*) (eq? name '/)
         (eq? name '=) (eq? name '<) (eq? name '>) 
         (eq? name '<=) (eq? name '>=))
     (>= (length vals) 2))
    (else #f)))

;This will be our main body function which will do all the heavy lifiting for the checking of syntax

;Along with the main body functions we will need to implement some functions such as member?

;pre: lst is a list, x is an atom
(define (member? x lst)
  (cond ((null? lst) #f)
        ((eq? x (car lst)) #t)
        (else (member? x (cdr lst)))))
;post: returns whether an element x is a member of lst

;pre: lst is a list
(define (duplicates? lst)
  (cond ((null? lst) #f)
        ((member? (car lst) (cdr lst)) #t)
        (else (duplicates? (cdr lst)))))

;returns: returns true if the list lst contains duplicates

;this is a function that gathers errors from a list of expressions
;this is helpful when it comes to a function that has multiple errors \
;this code is wrong someone fix it 
(define (gathers errs lst env)
  (if (null? lst)
      errs
      (gather (append errs (syntax-checker (car lst) env))
              (cdr lst) env)))
         

;pre condtion

;post condition

;Design idea

;Base Case

;inductive step

;inductive hypothesis



;pre condition: expr is an expressions
( define (syntax-checker expr env)
   (cond
     ;The following will be the base cases
     ;This is for the constants
    ((constant? expr) #t)
    ;This is for Varibles
    ((symbol? expr)(var? expr env))
    
    ((and (pair? expr) (eq? (car expr) 'quote))
     (and (= (length expr) 2)))
    
    ;This is used for simiple arethmetic like + - * and /
   ((and(pair? expr)(member? (car expr) primitive-names))
    (and(conditions(first expr)(cdr expr))
        (check-args(cdr expr) env)))

   ;This is used to check the If statement
   ((and(pair? expr)(eq?(car expr) 'if))
       (check-if expr env))
   

;This will be used to check the and statment and the or statment
   ((and(pair? expr)(or(eq?(car expr) 'and)(eq?(car expr) 'or))
    (check-and-or expr env)))

   ((and(pair? expr)(eq?(car expr) 'lambda))
    (check-lambda expr env))

 (else #f )))





    
  
       

   ;This is used to check the arguments are well formed
   ;SHould be used after checking the condtions that way program can tell
   ; something is invalid with the inputs

(define (check-args args env)
  (cond ((null? args) #t)
        ((and (syntax-checker (car args) env)
              (check-args (cdr args) env)))
        (else #f)))







    
     
;If implemementer
; if follows
;IF this , else that


(define (check-if expr env)
  (and(=(length expr )4)
      (syntax-checker(cadr expr) env)
      (syntax-checker(caddr expr) env)
      (syntax-checker(cadddr expr) env)))

;tests
;(check-if '(if (= 10 10) #t #f) '()) ; => #t
;;(check-if '(if (= 10 10) #t) '())    ; => #f
;;(check-if '(if 10 #t #f) '())        ; => #t
;NOTE: when testing, test on terminal or at the bottom since syntax-checker references constant?
; and that is towards the bottom of the code
;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;This is a checker for and
;As we know and can have multiple argumeans for example
;((and(eq? (car lst) 1)(eq? (car lst) 2)(eq? (car lst) 2)))
;it can even have one statment like (and (= 1 1)) would return true
;And can also just be itself: (And) and returns true

;Design idea:
;i think we should treat each entity of and as its own, so we should probably reffer each
;expression into check-arguments and check if the expressions are valid, that way no matter if we have
; 1 and condtion or 100 our program should always work with. And since Check-args automaticly goes into
;syntax checker to check we can see that this implementation will be valid assuming Check-args and
;check-synatx is correct


;(define(check-and expr env)
     ;(check-args(cdr expr) env))

;NOTE: it seems like OR and AND follow the same implementation so we should reffer both or and AND to the same function
;(define(check-or expr env)
  ;(check-args(cdr expr env)))
(define(check-and-or expr env)
  (check-agrs(cdr expr) env))

;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

;What should lambda have?
;Lambda should consist of (lambda then the paramaters and then the body
;So something like (lambda (x 10) datum)
(define(check-lambda  expr env)
  (and(=(length expr ) 3)
      (list?(cadr expr)) ;This is because the params should always be in () form
      (is-symbol?(cadr expr))  
      (not(duplicates?(cadr expr))) ;Duplicates was implemented earlier in the program and is used to prevent bad syntax like (lambda( x  x))
      (syntax-checker(caddr expr) ; this checks the body
                     (append(cadr expr) env)))) 














;post returns error if a syntax error is found. 

;Helpers for syntax-checker 
;; ============================================================================

;pre: x is an s-expression
( define ( constant? x)
   (or (number? x) (boolean? x) (string? x)(char? x)))
;post: returns true if x is a number, boolean, string, or char.


(define (var? x env)
  (or (memq x env) (memq x primitive-names)))

;This is used for reccursion to check if a list or value is a symbol
(define(is-symbol? lst)
  (cond
    ((null? lst) #t)
    ((symbol?(car lst))(is-symbol?(cdr lst)))
    (else #f)))
;Cond is a very powerful function.
;Since cond is a special form it follows it's own rules meaning we will probably have to do a checker for cond as well.

;get back to this function later
;(define (check-cond expr env))