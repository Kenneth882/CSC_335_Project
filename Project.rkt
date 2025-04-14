;Members: Alexis Juarez, Hamim Choudhury, Kenneth Romero
;4/9/25
;TLS Project
;Professor Troeger. 



;This is our Project for CSC 335

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Project: TLS Interpreter in R5RS Scheme
;;
;; Description:
;; This project reimplements and formally analyzes the interpreter described
;; in Chapter 10 of *The Little Schemer*. The goal is to create a minimal
;; interpreter for a small subset of Scheme using only R5RS-compliant,
;; purely functional constructs.
;;
;; In addition to the implementation, this project focuses on formal reasoning,
;; including correctness proofs, syntax validation, and comparison with
;; DrRacket's built-in interpreter.
;;
;; ============================================================================
;; 1.1 Implement TLS in R5RS Scheme
;; - Translate the interpreter from Chapter 10 of TLS into pure R5RS Scheme.
;; - Use only functional constructs—no mutation, macros, or side effects.
;; - Provide short specifications for each function.
;; - Include working example programs written in TLS syntax that demonstrate
;;   evaluation behavior.
;;
;; ============================================================================
;; 1.2 Write a Syntax Checker for TLS
;; - Define valid TLS programs inductively (as a grammar or AST).
;; - Implement a function `(valid-tls? expr)` to verify well-formedness.
;; - Detect errors such as:
;;     - Bad `cond` or `lambda` expressions
;;     - Incorrect number of arguments for built-in functions
;;     - Use of undefined variables (may use environment model)
;;
;; ============================================================================
;; 1.3 Specify & Prove Environment Subsystem
;; - Formally define how environments and variable lookup should behave.
;; - Prove that `lookup-in-entry` and `lookup-in-table` behave correctly
;;   according to the specification.
;; - Replace current environment representation (e.g. name/value lists)
;;   with an alternative (e.g. list of (name . value) pairs).
;; - Prove the new representation satisfies the same formal spec.
;;
;; ============================================================================
;; 1.4 Prove Correct Use of Closures and Lexical Scope
;; - Define and explain closures and lexical scoping clearly.
;; - Show that your interpreter correctly forms closures by capturing
;;   the defining environment.
;; - Use structural induction and case analysis to prove that:
;;     - Closures behave consistently.
;;     - Lexical scope rules are preserved in all evaluation contexts.
;;
;; ============================================================================
;; 1.5 Prove TLS is Correct
;; - Define what "correct" means for your interpreter.
;;     (e.g., For every valid expression e, (value e) yields the intended result.)
;; - Formally prove that your interpreter implementation satisfies this
;;   definition of correctness.
;;
;; ============================================================================
;; 1.6 Explain Interaction with R5RS
;; - Analyze what TLS relies on from the underlying R5RS interpreter (e.g., DrRacket).
;; - Focus especially on:
;;     - Primitive operations (like +, car, cons)
;;     - Function application mechanics
;;     - How much evaluation is performed by TLS vs. by Scheme itself
;;
;; ============================================================================
;; 1.7 Add Recursion to TLS using the Y-Combinator
;; - Extend TLS to support recursive functions using the Y-combinator
;;   (i.e., recursion without named functions).
;; - Prove that the Y-combinator implementation is correct.
;; - Demonstrate interesting recursive examples written in TLS syntax
;;   (e.g., factorial, Fibonacci, length).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 1.1 Implement TLS in R5RS Scheme

;In chapter 10 of TLS we were introduced to an interpreter and our job is to turn it into code in R5RS.


;The first part we are introduced to in the chapter is the lookup code, which is basiclly a hashmap in other languages.
;The lookup takes in two parameters, the name you are looking for and the pair of lists, the first one which must be a set(Would need to implmement a checker?)
;The lists must also be equal length.


; This is used to build the lists, ensuring the specifications of a "hashmap" where each list has a key value pair
; and the lenght of both of the lists is equal



;COMMENTS FOR US: Put any ideas or what you plan to work on/improve or if stuck on something.
;; ============================================================================








;BASIC HELPER FUNCTIONS
;; ============================================================================

; This is the basic atom function which will check when an element is an atom and saves us from redundent code
( define ( atom? x)
     (and (not (pair? x)) (not (null? x))))

;This is a simple helper function that can be callled that counts the number of lists
(define (count lst)
  (if (null? lst)
      0
      (+ 1 (count (cdr lst)))))

;IN TLS first refers to car
( define first car)

;IN TLS second refers to cadr
(define second cadr)

(define third  caddr)

;IN TLS extend-table refers to cons
( define extend-table cons)

;short program used to add1
(define (add1 n)
  (+ n 1))
; short program used to subtract by 1
(define( sub1 n)
  (- n 1))



            




;TLS FUNCTIONS
;; ============================================================================

;This is logic
;;;;;NEEDS WORK( im not entirly sure if this is correct
(define (build-entry names values)
  ;In TLS it says that only the first list must be a set so we just check the first list
  (check-set names) 
  ;Im thinking for this we use some tree properties with count to check the length(Done) you guys can double check
  ;This should for both nested and regular lists
  (check-eq-len names values)
  ;this should jus return the inputed lists 
  (list names values))



( define new-entry build-entry)
; we probably need to add somehting that adds the input to it 

;This function will tell us if a list is a set or if its not.
(define (check-set lst )
  (cond
    ((null? lst)
     '())
    ((member (car lst) (cdr lst))
     (set-f))
    (else (cons (car lst)
                (check-set (cdr lst))))))




;This checks if two lists have the equal length, should work for both nested and regular lists
;I think troger would prefer a bunch of helper functions like (set-f) so if you guys want to alter this to match that feel free to
(define (check-eq-len list1 list2)
  (if (= (count list1) (count list2))
      #t
     eq-list-f))  



;LOOKUP FUNCTIONs
;; ============================================================================
(define (lookup-in-entry name entry entry-f)
  (lookup-in-entry-helper name
                        (first entry)
                        (second entry)
                        entry-f
                        ))

;This is supposed to check if the name is in the values
( define (lookup-in-entry-helper name names values entry-f)
   (cond
     ((null? names)(entry-f name))
     ((eq?(car names) name)
      (car values))
     (else
      (lookup-in-entry-helper
       name
       (cdr names)
       (cdr values)
       entry-f
       ))))

;;;This is for table lookup

( define (lookup-in-table name table table-f)
   ( cond
      ((null? table)(table-f name))
      (else
       (lookup-in-entry name
                        (car table)
                        (lambda(name)
                          (lookup-in-table name
                                           (cdr table)
                                           table-f))))))


  
   






          
;Tests
;(lookup-in-entry 'wine '(appetizer entrée beverage) '(beer beer beer))
;(lookup-in-entry 'beverage '(appetizer entrée beverage) '(beer beer beer))




;ACTION FUNCTIONS
;; ============================================================================


;Is supposed to tell the action of the atom
(define (atom-to-action e)
  (cond
     ((number? e) *const)
     ((eq? e #t)  *const)
     ((eq? e #f)  *const)
     ((eq? e 'cons) *const)
     ((eq? e 'car)  *const)
     ((eq? e 'cdr)  *const)
     ((eq? e 'null?) *const)
     ((eq? e 'eq?)   *const)
     ((eq? e 'atom?) *const)
     ((eq? e 'zero?) *const)
     ((eq? e 'add1)  *const)
     ((eq? e 'sub1)  *const)
     ((eq? e 'number?) *const)
     (else *identifier)))

;Defenition of list-to-action
(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote) 
        *quote)
       ((eq? (car e) 'lambda)
        *lambda)
       ((eq? ( car e)('cond))
        *cond)
       (else *application)))
    (else *application)))


;The following function prodoucess the correct action for each possible S-expression
( define (expression-to-action e)
   ( cond
      ((atom? e)(atom-to-action e))
      ( else
        ( list-to-action e))))

;Actions to constants
( define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build ('primative) e))))

(define (*quote e table)
  (text-of e))

(define text-of second)

(define (value e)
  (meaning e ('())))

( define (meaning e table)
   (lambda ( e table)
     ((expression-to-action e) e table)))

( define ( *identifier e table)
   (lookup-in-table e table initial-table))

( define (initial-table name)
   
     ( car ('())))

( define (*lambda e table)
   (build(' non-primitive)
         (cons table (cdr e))))

( define table-of first)
( define formals-of second)

; need to write defeniton for third
(define body-of third)

(define (evcon lines table)
  (cond
    ((else? (question-of (car lines)))
     (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))


(define (else? x)
  (cond
    ((atom? x)(eq? x(' else)))
    (else #f)))

(define question-of first)
(define answer-of second)

(define (*cond e table)
  (evcon(cond-lines-of e) table))

(define cond-lines-of cdr)

(define(evlis args table)
  (cond
    ((null? args)('()))
    (else
     (cons(meaning(car args)table)
          (evlis(cdr args) table)))))

( define (*application e table)
   (apply
    (meaning(function-of e ) table)
    (evilis(arguments-of e) table)))

(define function-of car)
(define arguments-of cdr)

( define (primitive? l)
   (eq?(first l) (' primitive)))

(define (non-primitive l)
  (eq? (first l)(' non-primitive)))

(define (applyi fun vals)
  (cond
    ((primitive? fun)
     (apply-primitive(second fun) vals))
    ((non-primitive? fun)
     (apply-closure
      (second fun) vals))))


(define apply-primitive
  (lambda (name vals)
    (cond
     ((eq? name 'cons)
      (cons (first vals) (second vals)))
     ((eq? name 'car)
      (car (first vals)))
     ((eq? name 'cdr)
      (cdr (first vals)))
     ((eq? name 'null?)
      (null? (first vals)))
     ((eq? name 'eq?)
      (eq? (first vals) (second vals)))
     ((eq? name 'atom?)
      (:atom? (first vals)))
     ((eq? name 'zero?)
      (zero? (first vals)))
     ((eq? name 'add1)
      (add1 (first vals)))
     ((eq? name 'sub1)
      (sub1 (first vals)))
     ((eq? name 'number?)
      (number? (first vals))))))

(define :atom?
  (lambda (x)
    (cond
     ((atom? x) #t)
     ((null? x) #f)
     ((eq? (car x) 'primitive) #t)
     ((eq? (car x) 'non-primitive) #t)
     (else #f))))


(define (apply-closure closure vals)
  (meaning (body-of closure)
           (extend-table
            (new-entry
             (formals-of closure)
             vals)
            (table-of closure))))
  


   



;ERROR FUNCTIONS
;; ============================================================================

;this is a helper function that displays if an error is found, in this case it is used to tell if the inputed list
; is a set or not
(define (set-f)
  (begin
    (display "Error: Not a set,duplicate elements found.")
    (newline)
    #f))

( define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))

( define( table-f name)
   ( begin
      (display "Error:")
      (display name)
      ( display "Not found in the table")
      (newline)#f))
               
(define(eq-list-f)
   (begin
        (display "Error: Lists are not of equal length.")
        (newline)
        #f))




  

;; ============================================================================

;Some small tests ( add more as more is added on and expand) Not Entirley correct as of rn but fix to match with book 

;
;(new-entry '((beverage dessert)
                      ;((food is) (number one with us))))

 ;(new-entry '((beverage dessert yo)
                      ;((food is) (number one with us))))
;(check-set '( 2 3 4 5 5))

;( count '( 1 3 4 )














