;Members: Alexis Juarez, Hamim Choudhury, Kenneth Romero
;TLS Project
;Professor Troeger



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
; and the length of both of the lists is equal



;COMMENTS FOR US: Put any ideas or what you plan to work on/improve or if stuck on something.
;; ============================================================================
; 4/14/25 - Hamim (Comments Below)
; So 1.1 of the project is telling us to make the functions in chapter 10 of the book ourselves, in R5RS scheme. The functions that they have
; are
; 1) lookup-in-entry (this takes two arguments, name and entry)
; 2) lookup-in-entry-helper (this is the helper function for #1. This is used when name is not found in the first list of an entry)
; 3) extend-table (this is like cons)
; 4) lookup-in-table (takes three arguments, name, table, and table-f)
; 5) expression-to-action (this produces the correct function for each possible S-expression. action == function)
; 6) atom-to-action
; 7) list-to-action
; 8-16) value, meaning, *const, *quote, *identifier, *lambda, *application, *evcon, *else
; 17-22) primitive?, non-primitive?, apply, apply-primitive, atom?, apply-closure
; Now how do we approach this? In chapter 10 of the book we have some functions written completely and we just need to convert that to R5RS,
; and some do not. Kenneth already began to create the basic helper functions and write the functions in Scheme (4/14/25). We started off by
; first creating the basic helper functions, the ones that are in the chapter and commonly used in TLS and then we went through the list one
; by one and made the functions. 


; 4/16/25 - Hamim (Comments Below)
; Today was just completing the build function in TLS, what this function does is that it returns an entry if it satisfies two conditions. The
; first condition being that the names list does not contain duplicates, aka is a set. And the second condition being that the values list and
; names list are of equal length. Both of the conditions have their own function, check-set and check-equal-len-list. Kenneth had already begun
; a basic outline of it, I just added onto it and finalized it. Alexis and me were working on the pre and post conditions as well.


; 4/17/25 - Hamim (Comments Below)



; 4/19/25 - Hamim (Comments Below)








; BASIC HELPER FUNCTIONS. These are basic functions such as atom?, add1, etc.
; Or they are functions that have been translated to R5RS Scheme.
;; ============================================================================

; This is the atom function which will check when an element is an atom and saves us from
; using redundant code. TLS also assumes this function is built in.
(define (atom? x)
  (and (not (pair? x)) (not (null? x))))


;This is a simple helper function that can be called that counts the number of elements in a list
(define (count-elements lst)
  (if (null? lst)
      0
      (+ 1 (count-elements (cdr lst)))))


;A function used to add by 1
(define (add1 n)
  (+ n 1))


;A function used to subtract by 1
(define (sub1 n)
  (- n 1))


;In TLS first refers to car
(define first car)


;In TLS second refers to cadr
(define second cadr)


;In TLS third refers to caddr
(define third caddr)


;In TLS extend-table refers to cons
(define extend-table cons)


; There are certain functions that we do not need to make as they are already in Scheme. For example,
; append, member?, and pair?.






;; ===========================================================================
; This is the lookup-in-entry function. Accompanied with it is the lookup-in-entry-helper.
;; ===========================================================================

;Design Idea:
;when looking up the entry there will be 3 possible cases, one where the name is found in entry, it will then return the associated value with the name.
;If it does not exist it will return the associated value once the entry-f is called.
;The third case will be if no name is given aka an empty char/string, then we call the entry-f function.
; ___________________
;[_______ayp|nyp_____]------>(first entry)= ayp----->(second entry) =nyp -------->(if ayp and nyp = name then we return entry-f)
;                                                                                   (needs helper)

;ayp: the first tables (ill go more in detail later i gotta push)
;nyp: the remaining tables


;pre/specs: takes three arguments, name (what we are looking for), entry (list of names and list of values),
;and entry-f, an error function if name not found.
(define (lookup-in-entry name entry entry-f)
  (lookup-in-entry-helper name
                        (first entry)
                        (second entry)
                        entry-f
                        ))
;post: returns the value associated with name if it exists in entry. If it does not exist, calls the entry-f function.


(define (lookup-in-entry-helper name names values entry-f)
   (cond
     ((null? names)(entry-f name))
     ((eq? (car names) name) (car values))
     (else
      (lookup-in-entry-helper
       name
       (cdr names)
       (cdr values)
       entry-f
       ))))

; Testing the function
; (define entry '((x y z) (1 2 3)))
; (lookup-in-entry 'x entry (lambda (name) 'not-found-in-entry)) ;returns 1
; (lookup-in-entry 'a entry (lambda (name) 'not-found-in-entry)) ;returns not-found-in-entry
; (lookup-in-entry 'entree '((appetizer entree beverage) (ar luka lebron)) (lambda (name) 'not-found)) ;returns luka





;; ===========================================================================
; This is the lookup-in-table function. 
;; ===========================================================================
;pre/specs: this takes three arguments, name (what we are looking for), table (it is a list of entries),
; and table-f (an error function if name is not found)
(define (lookup-in-table name table table-f)
   (cond
     ((null? table)(table-f name))
     (else
      (lookup-in-entry name
                       (car table)
                       (lambda (name)
                         (lookup-in-table name
                                          (cdr table)
                                           table-f))))))
;post: returns the value associated with name if it is found in table. if it does not exist, calls the table-f function.

;Testing the function
; (define table '(((entree dessert)
;                (spaghetti spumoni))
;               ((appetizer entree beverage)
;                (food tastes good))))
; (lookup-in-table 'entree table (lambda (name) 'not-found)) ;returns spaghetti
; (lookup-in-table 'dessert table (lambda (name) 'not-found)) ;returns spumoni
; (lookup-in-table 'appetizer table (lambda (name) 'not-found)) ;returns food
; (lookup-in-table 'snacks table (lambda (name) 'not-found)) ;returns not-found



            




;; ============================================================================
; TLS FUNCTIONS
; In TLS, it asks a crucial question, "How can we build an entry from a set of names and a list of values?"
; It then proceeds to tell us that we should try and build our examples with the function of
; (define new-entry build). And this is ultimately saying new-entry = build. So we need to make a build function.
;; ============================================================================





;; ===========================================================================
; This is the check-set function. It checks whether or not the list has duplicates.
; Sets cannot have duplicates.
;; ===========================================================================
;pre: list1 is a list
(define (check-set list1)
  (cond
    ((null? list1) #t)
    ((member (car list1) (cdr list1)) #f)
    (else
     (check-set (cdr list1)))))
;post: returns #t if list1 is a set and #f if it is not a set

;Testing the function
; (check-set '())           ;returns #t
; (check-set '(1 2 3 4))    ;returns #t
; (check-set '(1 2 2 3))    ;returns #f





;; ===========================================================================
; This is the check-equal-len-list function. It checks whether two lists are of equal length. 
;; ===========================================================================
;pre: list1 and list2 are lists
(define (check-equal-len-list list1 list2)
  (cond
    ((and (null? list1) (null? list2)) #t)
    ((or (null? list1) (null? list2)) #f)
    (else
     (check-equal-len-list (cdr list1) (cdr list2)))))
;post: returns #t or #f based on if the lists are of equal length or not


;Testing the function
; (check-equal-len-list '(x y z) '(10 20 30))  ;returns #t
; (check-equal-len-list '() '(1 2 3))          ;returns #f
; (check-equal-len-list '(x y z) '())          ;returns #f
; (check-equal-len-list '() '())               ;returns #t
; (check-equal-len-list '(a b c d) '(1 2 3))   ;returns #f





;; ===========================================================================
; This is the build function. It creates entry and validates that the names list has no dupes and
; the names list and values list are the same length. And then it returns the entry.
;; ===========================================================================

;pre: this takes two? three? arguments. names, values, and build-f (an error function). FIX THIS PRE CONDITION!
(define (build names values build-f)
  (cond
    ((not (check-set names)) (build-f "Names error. Names cannot have duplicates"))
    ((not (check-equal-len-list names values)) (build-f "Value error. Names and value must be equal length"))
    (else
     (list names values))))
;post: returns an entry if names has no duplicates and names and values are of equal length. otherwise, returns
;the appropriate error message. 


;Testing the function
; (build '(x y z) '(1 2 3) (lambda (message) message))     ;returns ((x y z) (1 2 3))
; (build '(x y z) '(1 2 3 4) (lambda (message) message))   ;returns value error.
; (build '(x x y z) '(1 2 3 4) (lambda (message) message)) ;returns name error




          





;; ============================================================================
; Action Functions
; In chapter 10 of TLS, we once again meet the use of value. And value is the function that returns
; the natural value of expressions. After that, we then get introduced to the different action functions
; There are different types: *const, *quote, *identifier, *lambda, *cond, and *application. And to represent
; we use action functions. We have atom-to-action, expression-to-action, and list-to-action. 
;; ============================================================================

; TLS DOES SOMETHING SNEAKY. THEY HAVE ANOTHER BUILD FUNCTION. THIS IS FOR PRIMITIVES. AND THIS IS NEEDED
; IF WE WANT TO TEST THE expression-to-action function.
(define (build-for-prims tag value)
  (list tag value))


(define (primitive? l)
  (eq? (first l) 'primitive))


(define (non-primitive? l)
  (eq? (first l) 'non-primitive))


;Action for constants
(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build-for-prims 'primitive e))))

;Action for quote
(define (*quote e table)
  (text-of e))


(define text-of second)


(define (value e)
  (meaning e '()))


(define (meaning e table)
  ((expression-to-action e) e table))


;Action for identifier
(define (*identifier e table)
   (lookup-in-table e table initial-table))


(define (initial-table name)
  (car '()))


;Action for lambda
(define (*lambda e table) 
  (build('non-primitive)
        (cons table (cdr e))))


(define table-of first)
(define formals-of second)
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
    ((atom? x) (eq? x 'else))
    (else #f)))


(define question-of first)
(define answer-of second)


;Action for cond
(define (*cond e table)
  (evcon(cond-lines-of e) table))


(define cond-lines-of cdr)


(define (evlis args table)
  (cond
    ((null? args)('()))
    (else
     (cons (meaning (car args) table)
           (evlis (cdr args) table)))))


;Action for application
(define (*application e table)
   (apply
    (meaning(function-of e ) table)
    (evilis(arguments-of e) table)))


(define function-of car)
(define arguments-of cdr)


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
       (atom? (first vals)))
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
  


;; ===========================================================================
; This is the atom-to-action function. This was already given to us in TLS chapter 10. The purpose of this is
; to decide how to evaluate an expression. And returns the correct "action". 
;; ===========================================================================
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





;; ===========================================================================
; This is the list-to-action function. This was also given in TLS. The purpose of this is to handle expressions
; that are not atoms, hence why we have quote, lambda, and cond as a comparison for our eq? and return it.
; Also deals with *application. 
;; ===========================================================================
(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote) *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond) *cond)
       (else *application)))
    (else *application)))




;; ===========================================================================
; This is the expression-to-action function. This was also given in TLS. The purpose of this can be thought of
; as the main function, it calls both of the two previous functions given what we have inputted. And then the other
; two can be considered helper functions that do all of the work. 
;; ===========================================================================
(define (expression-to-action e)
  (cond
    ((atom? e)(atom-to-action e))
    (else
     (list-to-action e))))


;Testing the function. I think these are all correct, not sure though.
((expression-to-action 42) 42 '()) ;returns 42
((expression-to-action #f) #f '()) ;returns #f
((expression-to-action #t) #t '()) ;returns #t
((expression-to-action 'car) 'car '())
((expression-to-action 'cdr) 'cdr '())
((expression-to-action 'null?) 'null? '())
((expression-to-action 'eq?) 'eq? '())
((expression-to-action 'atom?) 'atom? '())
((expression-to-action 'zero?) 'zero? '())
((expression-to-action 'add1) 'add1 '())
((expression-to-action 'sub1) 'sub1 '())
(expression-to-action '(quote hello))
(expression-to-action '(lambda (x) x))
(expression-to-action '(cond ((#t 1))))
(expression-to-action '(add1 4))
(expression-to-action '((lambda (x) x) 5))







   



;; ============================================================================
; Error Functions
; In chapter 10 of TLS, we get introduced to parameters within our function that ends in -f. For example, we
; have set-f, entry-f, table-f, etc, etc. These are known as error functions. Because we don't want to actually
; write an else clause and then an error message.
;; ============================================================================

;This is an error function set-f, which returns an error message if the input is not a set.
(define (set-f)
  (begin
    (display "Error: Not a set, duplicate elements found.")
    (newline)
    #f))


;This is an error function entry-f that returns an error message if the name we are looking for/searching is
;not in the values list.
(define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))


;This is an error function table-f which returns an error message if the name we are looking for/searching is
;not in the table. 
(define(table-f name)
   (begin
      (display "Error:")
      (display name)
      (display "Not found in the table")
      (newline)#f))


;This is an error function eq-list-f which returns an error message if the two lists, are not of equal length.
(define(eq-list-f)
   (begin
        (display "Error: Lists are not of equal length.")
        (newline)
        #f))


(value '5)  ; Should return 5
(value '#t) ; Should return #t
(value '(quote hello)) ; Should return hello

(value '(cond (#t 'hello))) ; Should return hello
(value '(cond (#f 'wrong) (else 'correct))) ; Should return correct


;THESE TWO DO NOT WORK. FIX THIS LATER
; (value '((lambda (x) x) 5)) ; Should return 5
; (value '((lambda (x y) (cons x y)) 'a 'b)) ; Should return (a . b)
