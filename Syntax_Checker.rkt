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
;Now the question has to be asked if (cond, else, and , or, if ) need any checking?
;We know cond MUST end with an else so we have to keep that into consideration, else must also have
; some value come before it, as must and, and or, and if must only contain 2 possible outputs.
;In or TLS interpreter there were also some translations that we did from basic R5RS So we should also add that into the primitive-names pool.
; A simple way to maybe tackle the problem is to maybe have a cases function where our main body could refer to so once it finds the name of the primitive it then checks the
;amount of conditions it shoudl have, so as an example atom? should only have 1 since its only checking one piece of information.

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

;pre condtion

;post condition

;Design idea

;Base Case

;inductive step

;inductive hypothesis




( define (syntax-checker expr env)
   (cond
     ;The following will be the base cases
     ;This is for the constants
    ((constant? expr) #t)
    ;This is for Varibles
    ((symbol? expr)(var? expr env))
    
    ((and (pair? expr) (eq? (car expr) 'quote))
     (and (= (length expr) 2)))


    
    ))


;Helpers for syntax-checker
;; ============================================================================
( define ( constant? x)
   (or (number? x) (boolean? x) (string? x)(char? x)))

(define (var? x env)
  (or (memq x env) (memq x primitive-names)))


     