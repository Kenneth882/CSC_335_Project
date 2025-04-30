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

;4/13/25 - Alexis (Comments Below)
;1.1 of the project is based on TLS chapter 10. The implementations of the the function.
;One of the important things I have noticed are most functions are tail recursive (lookup-in-entry-helper, lookup,entry, etc.)
;This will be crucial for the proofs required from 1.5 so for now I have made a seperate file containing the proofs. 
;Before jumping into the proofs kenneth proposed we finish building the interperter so for now the proofs are not needed. 
;However, I labled each code with either T Recursion or Recursion so we will know in the future what proof will be needed
;For each function.


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
; a basic outline of it, I just added onto it and finalized it. Alexis and myself were working on the pre and post conditions as well.


; 4/17/25 - Hamim (Comments Below)
;Action functions.


; 4/28/25 - Alexis (Comments Below)
; Since most of the interpreter is done Hamim volunteered to clean up the code. We came accross an issue when using the test expressions 
; Professor Troeger provided. We concluded it was due to apply, instead of using the apply we implemented through TLS, the function *application
; was using the built in apply. After discovering that issue, Hamim uncovered other issues with our initial-table and new entry.
; After looking into apply I started working on syntax-checker. Kenneth already started the outline. I added the pre and post condition.
; I also implemented functions such as member?, duplicates, check-cond(not fully done), and error messages.


;4/29/25 - Hamim (Comments Below)
; Adding on to Alexis's comments. Yes, there were errors when certain test cases were run. These errors were annoying because it let to the same few
; functions. And those functions were linked to other functions. It was like a loop of errors in a sense. There were two main issues. My build function,
; the apply function, and the primitive and non-primitive functions. The root errors were 1) something was not a procedure, mcar errors, and mcdr errors.
; In order to solve this, I spent all of today reading TLS carefully. I noticed that we did have some missing functions, spelling errors, and we made some
; functions a little more complex than it should have been. We were missing quote, lambda, and our action functions were wrong as well. The value and meaning
; were also incorrect.


;4/30/25 - Hamim (Comments Below)
;Cleaning up code, making sure test cases all run. In order to make the output look nicer, I added two (newline) so it is easier to see the output and what
;section of code corresponds to what.






; BASIC HELPER FUNCTIONS. These are basic functions such as atom?, add1, etc.
; Or they are functions that have been translated to R5RS Scheme.
; Also included in this section are functions from TLS that we will use for our
; more complex functions, like action-to-action, action-to-list, etc.
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


;In TLS, this is the else? function
(define (else? x)
  (and (atom? x) (eq? x 'else)))


;In TLS, this is returning the car of a cond
(define question-of first)


;In TLS, this returns the cadr of a cond
(define answer-of second)


;In TLS, this gives the cdr of a cond
(define cond-lines-of cdr)


;In TLS, this extracts the car of an application
(define function-of car)


;In TLS, this extracts the cdr of an application
(define arguments-of cdr)


;In TLS, this returns the data inside a quote
(define text-of second)


;In TLS, this gets the environment from a closure
(define table-of first)


;In TLS, this gets the parameters from a closure
(define formals-of second)


;In TLS, this returns the caddr
(define body-of third)


;Not in TLS, but defined this because it is easier to do rather than type out constantly,
;This returns #t when an atom is a number, boolean, or primitive procedure. Or false otherwise.
; This is used to determine if an atom should be treated like a constant or a primitive procedure.
(define (const-atom? a)
  (or (number? a)
      (eq? a #t)
      (eq? a #f)
      (memq a '(cons car cdr null? eq? atom? zero? add1 sub1 number?))))


;This makes a new table. It takes formal parameters, values, and the current table. And then
;using (define new-entry build), it creates a new entry and then adds it to the front.
(define (extend-table formals vals table)
  (cons (build formals vals) table))


;This is a really important function, possibly one of the most important ones. This just evaluates everything.
;A lot of the test cases in the book and from Professor Troeger use this for test cases.
(define (value e)
  (meaning e '()))


;Made because we assume that expression-to-action works. This evaluates the expression in a given
;environment.
(define (meaning e table)
  ((expression-to-action e) e table))


;So this was a main reason why our code was not working. In TLS, it gives us initial-table. However, if we carefully
;read it, it says that this should never be used really. So this is just like a fall back and gives an error. 
(define (initial-table name)
  (error "Unbound identifier" name))


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


(define (lookup-in-entry name entry entry-f)
  (let loop
    ((names (first entry))
     (values (second entry)))
    
    (cond
      ((null? names) (entry-f name))
      ((eq? (car names) name) (car values))
      (else
       (loop (cdr names) (cdr values))))))

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
      (lookup-in-entry name (car table)
                       (lambda (name) (lookup-in-table name (cdr table) table-f))))))
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
(define build list)
(define new-entry build) ;this is straight from TLS. Need to fix this section.

;post: returns an entry if names has no duplicates and names and values are of equal length. otherwise, returns
;the appropriate error message. 


;Testing the function
;(build '(x y z) '(1 2 3))     ;returns ((x y z) (1 2 3))
; (build '(x y z) '(1 2 3 4))   ;returns value error.
; (build '(x x y z) '(1 2 3 4)) ;returns name error




          





;; ============================================================================
; Action Functions
; In chapter 10 of TLS, we once again meet the use of value. And value is the function that returns
; the natural value of expressions. After that, we then get introduced to the different action functions
; There are different types: *const, *quote, *identifier, *lambda, *cond, and *application. And to represent
; we use action functions. We have atom-to-action, expression-to-action, and list-to-action. 
;; ============================================================================

(define (primitive? fun)
  (and (pair? fun) (eq? (first fun) 'primitive)))


(define (non-primitive? fun)
  (and (pair? fun) (eq? (first fun) 'non-primitive)))


;Action for constants
(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))


;Action for quote
(define (*quote e table)
  (text-of e))


;Action for identifier
(define (*identifier e table)
  (lookup-in-table e table initial-table))


;Action for lambda
(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e))))


;; evcon : list-of-cond-clauses table → value
(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))



;Action for cond
(define (*cond e table)
  (evcon (cond-lines-of e) table))


;Takes a list of arguments and a table, and then returns a list composed of the meaning
;of each argument.
(define (evlis args table)
  (if (null? args)
      '()
      (cons (meaning (car args) table) (evlis (cdr args) table))))


;Action for application
(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))


;In TLS, the function was originally called "apply", but Scheme R5RS already has its built in apply,
;so I made another one specifically called tls-apply.
(define (tls-apply fun vals)
  (cond
    ((primitive? fun) (tls-apply-primitive (second fun) vals))
    ((non-primitive? fun) (tls-apply-closure (second fun) vals))
    (else
     (error "tls-apply: not a function" fun))))


(define (tls-apply-primitive name vals)
  (cond
    ((eq? name '+) (apply + vals))
    ((eq? name 'cons) (cons (first vals) (second vals)))
    ((eq? name 'car) (car (first vals)))
    ((eq? name 'cdr) (cdr (first vals)))
    ((eq? name 'null?) (null? (first vals)))
    ((eq? name 'eq?) (eq? (first vals) (second vals)))
    ((eq? name 'atom?) (atom? (first vals)))
    ((eq? name 'zero?) (zero? (first vals)))
    ((eq? name 'add1) (+ (first vals) 1))
    ((eq? name 'sub1) (- (first vals) 1))
    ((eq? name 'number?) (number? (first vals)))
    (else
     (error "unknown primitive" name))))


(define :atom?
  (lambda (x)
    (cond
     ((atom? x) #t)
     ((null? x) #f)
     ((eq? (car x) 'primitive) #t)
     ((eq? (car x) 'non-primitive) #t)
     (else #f))))


(define (tls-apply-closure closure vals)
  (let*
      ((saved (first closure))
       (formals (second closure))
       (body (third  closure))
       (new-env (extend-table formals vals saved)))
    (meaning body new-env)))
  


;; ===========================================================================
; This is the atom-to-action function. This was already given to us in TLS chapter 10. The purpose of this is
; to decide how to evaluate an expression. And returns the correct "action". 
;; ===========================================================================
(define (atom-to-action e)
  (cond
    ((const-atom? e) *const)
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
       ((eq? (car e) 'quote)  *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond)   *cond)
       (else *application)))
    (else *application)))



;; ===========================================================================
; This is the expression-to-action function. This was also given in TLS. The purpose of this can be thought of
; as the main function, it calls both of the two previous functions given what we have inputted. And then the other
; two can be considered helper functions that do all of the work. 
;; ===========================================================================
(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))


;Testing the function. I think these are all correct, not sure though.
;((expression-to-action 42) 42 '())           ;returns 42
;((expression-to-action #f) #f '())           ;returns #f
;((expression-to-action #t) #t '())           ;returns #t
;((expression-to-action 'car) 'car '())       ;returns (primitive car)
;((expression-to-action 'cdr) 'cdr '())       ;returns (primitive cdr)
;((expression-to-action 'null?) 'null? '())   ;returns (primitive null?)
;((expression-to-action 'eq?) 'eq? '())
;((expression-to-action 'atom?) 'atom? '())
;((expression-to-action 'zero?) 'zero? '())
;((expression-to-action 'add1) 'add1 '())
;((expression-to-action 'sub1) 'sub1 '())
;(expression-to-action '(quote hello))
;(expression-to-action '(lambda (x) x))
;(expression-to-action '(cond ((#t 1))))
;(expression-to-action '(add1 4))
;(expression-to-action '((lambda (x) x) 5))
(newline)
(newline)






   



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





;my own test cases
;(value '5)                   ; Should return 5
;(value '#t)                  ; Should return #t
;(value '(quote hello))       ; Should return hello
;(value '(cond (#t 'hello)))  ; Should return hello
;(value '(cond (#f 'wrong) (else 'correct))) ; Should return correct
(newline)
(newline)










;test cases from professor. these were posted on MS Teams.
(value '((lambda (x) (add1 x)) 3))
;this returns 4


(value '((lambda (x) (add1 x))
	 ((lambda (x) (add1 x)) 4)))
;this returns 6


(value '(((lambda (y)
            (lambda (x) (cons x y)))
          3)
         4))
;this returns (4 . 3)


(value '((lambda (x z)
           (cons x
                 ((lambda (x y) (cons z x))
                  3 4)
                 ))
         1 2))
;this returns (1 2 . 3)


(value '((lambda (f y)
          (f y))
        (lambda (x) (add1 x))
        4))
;this returns 5


(value '((lambda (f y)
	   (f y))
	 ((lambda (x) (cond ((number? x) add1)
			    (else (lambda (y) (cons x y)))))
	  (quote z))
	 3))
;this returns (z . 3)


(value '((lambda (x)
             ((lambda (f)
                (cons x ((lambda (x) (f x))
                         3)))
              (lambda (y) (cons x y))))
         2))
;this returns (2 2 . 3)
