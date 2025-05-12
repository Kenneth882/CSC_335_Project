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


; 4/12-Kenneth(Comments Below)
; 1.1 is basicly a translation of TLS from TLS language into R5RS. I do notice that some functions from the book are repeated so i think the outline
; for the interpreter would be to get the simple functions and helpers out of the way first, that way we can keep refering to them and avoid redundent code.
; Initially i wll focus on just pure translation and then after everything is translated I will focus on connecting the important components

; 4/13/25 - Alexis (Comments Below)
; 1.1 of the project is based on TLS chapter 10. The implementations of the the function.
; One of the important things I have noticed are most functions are tail recursive (lookup-in-entry-helper, lookup,entry, etc.)
; This will be crucial for the proofs required from 1.5 so for now I have made a seperate file containing the proofs. 
; Before jumping into the proofs kenneth proposed we finish building the interperter so for now the proofs are not needed. 
; However, I labled each code with either T Recursion or Recursion so we will know in the future what proof will be needed
; for each function.


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

; 4/14-Kenneth(Commments Below)
; I implememnted most of TLS straight from the book, some of the functions still need to be linked.Most of the test cases that i did work with the function
; on its own, however there are certain functions that connect that have some logical errors to them, so we will hopfully work on fixing that. Since TLS
; had some repeated functions that did diffrent things we still have to clean and fix that so that each function can past every test case.

; 4/14-Alexis(Comments Below)
; I reviewed the code Kenneth implemented and fixed some errors, and added some of the basic functions from the book TLS. 
; Kenneth explained the outline and how some of the functions are repeated and some of the logic in TLS is flawed.


; 4/16/25 - Hamim (Comments Below)
; Today was just completing the build function in TLS, what this function does is that it returns an entry if it satisfies two conditions. The
; first condition being that the names list does not contain duplicates, aka is a set. And the second condition being that the values list and
; names list are of equal length. Both of the conditions have their own function, check-set and check-equal-len-list. Kenneth had already begun
; a basic outline of it, I just added onto it and finalized it. Alexis and myself were working on the pre and post conditions as well.


; 4/17/25 - Hamim (Comments Below)
; Action functions.

; 4/19-Kenneth (Comments Below)
; Started on the Syntax checker for TLS.Since we have a lot of functions for TLS I decided to have two refrences, conditons and special conditions
; Conditions will be all the operations that can be easily checked such as some of the built in operations and some primitives. Since some
; operations will be more complex like lambada where we will probably have to reccur to check all the other operations inside it we can always refer
; to the condtions to show if the arguments inside them follow the correct format.


; 4/28/25 - Alexis (Comments Below)
; Since most of the interpreter is done Hamim volunteered to clean up the code. We came accross an issue when using the test expressions 
; Professor Troeger provided. We concluded it was due to apply, instead of using the apply we implemented through TLS, the function *application
; was using the built in apply. After discovering that issue, Hamim uncovered other issues with our initial-table and new entry.
; After looking into apply I started working on syntax-checker. Kenneth already started the outline. I added the pre and post condition.
; I also implemented functions such as member?, duplicates, check-cond(not fully done), and error messages.


; 4/29/25 - Hamim (Comments Below)
; Adding on to Alexis's comments. Yes, there were errors when certain test cases were run. These errors were annoying because it let to the same few
; functions. And those functions were linked to other functions. It was like a loop of errors in a sense. There were two main issues. My build function,
; the apply function, and the primitive and non-primitive functions. The root errors were 1) something was not a procedure, mcar errors, and mcdr errors.
; In order to solve this, I spent all of today reading TLS carefully. I noticed that we did have some missing functions, spelling errors, and we made some
; functions a little more complex than it should have been. We were missing quote, lambda, and our action functions were wrong as well. The value and meaning
; were also incorrect.


; 4/29-Kenneth(Comments Below)
; After My inital layout of the syntax checker i realized that some of the Design was not correct. We dont really need a special-checker since
; each of the functions like lambda,cond,if ect does its own unique thing so refering to that would be redundant.I'm still not finished with it but most of the
; basic operations are done.The specific TLS functions still need to be checked and also need to work on showing specific
; error messages instead of just outputting false.

; 4/29-Alexis (Comments Below)
; I realized how complicated Cond is when it comes to this since I will need the helper functions made for expression. 
; Although And and other functions were made, I only used syntax-checker we made.
; I also added specs to my previous function kenneth and I made. 
; And finished more basic functions.

; 4/30/25 - Hamim (Comments Below)
; Cleaning up code, making sure test cases all run. In order to make the output look nicer, I added two (newline) so it is easier to see the output and what
; section of code corresponds to what.


; 4/30/25 - Alexis (Comments Below)
; I implemented some finishing touches to 1.1 for we can present the code to the professor tomorrow. 
; I also cleaned up 1.2 file and added some specs we missed. 
; Fixed some errors as well.


; 5/8/25 - Hamim (Comments Below)
; So today was the first day that I was able to work on this for a while because I had exams + projects for other classes. However, I spent all day today working on
; two things. During our last interview (interview 1), professor told me to add more test cases and essentially make them more complex. That is what I did today, I
; was able to add test cases for all functions and made sure that they were fairly complex. The second thing I completed was Section 1.6 of the project. I worked with
; Alexis on this part.


; 5/9/25 - Hamim (Comments Below)
; Today's goal is to organize the interpreter so that the functions can all run (they all do, but it does not look organized). Also, today is fixing the specs, and adding
; more specs to each function. Alexis will also be joining in doing some of the specs and the pre/post conditions, and proofs. 












; Now how do we approach this? In chapter 10 of the book we have some functions written completely and we just need to convert that to R5RS,
; and some do not. Kenneth already began to create the basic helper functions and write the functions in Scheme (4/14/25). We started off by
; first creating the basic helper functions, the ones that are in the chapter and commonly used in TLS and then we went through the list one
; by one and made the functions. 


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


;This is a custom error message that we have made.
(define (error msg arg)
  (display "ERROR: ") (display msg) (display " ") (display arg) (newline))


;Not in TLS, but defined this because it is easier to do rather than type out constantly,
;This returns #t when an atom is a number, boolean, or primitive procedure. Or false otherwise.
; This is used to determine if an atom should be treated like a constant or a primitive procedure.

;pre: takes one argument which can be any Scheme value
;post: returns #t if the argument is a number, bool, one of the symbols in the list, or #f otherwise.
(define (const-atom? a)
  (or (number? a)
      (eq? a #t)
      (eq? a #f)
      (if
       (memq a '(cons car cdr null? eq? atom? zero? add1 sub1 number?))
       #t #f)))

;Testing the Function const-atom?
; (const-atom? 'add1)                                 ;returns #t
; (const-atom? 'sub1)                                 ;returns #t
; (const-atom? 'number?)                              ;returns #t
; (const-atom? 'false)                                ;returns #f
; (const-atom? '(1 2 3))                              ;returns #f
; (const-atom? '())                                   ;returns #f
; (const-atom? '(cons 1 2))                           ;returns #f
; (const-atom? (if (const-atom? 'add1) 'yes 'no))     ;returns #f
; (const-atom? (cdr '(#t #f 42)))                     ;returns #f
; (const-atom? (if (zero? 0) #t #f))                  ;returns #t
; (const-atom? (if (number? 5) 'number 'not-number))  ;returns #f




;===========================================================================================================
;This makes a new table. It takes formal parameters, values, and the current table. And then
;using (define new-entry build), it creates a new entry and then adds it to the front.

;pre: takes three arguments, formals (parameter names), vals(list of corresponding values), and table(list of entries).
;post: returns a new table with a new entry added to the front.

#|
=============================================================================================
Proof for extend-table:
;;Since this line of code has no recursion we will use proof by construction:

:Proof:
;(build formals vals) -> this create a proper entry,
;the cons prepends this entry to an existing table
; Therefore extend-table correctly implements environment extension by proof of construction.
=============================================================================================
|#

(define (extend-table formals vals table)
  (cons (build formals vals) table))
;===========================================================================================================




;===========================================================================================================
;Made because we assume that expression-to-action works. This evaluates the expression in a given
;environment.

;pre: e is an expression that will be evaluated. table is the currend environment
;post: returns the result of evaluating expression e in the table by using expression-to-action
(define (meaning e table)
  ((expression-to-action e) e table))
;===========================================================================================================




;===========================================================================================================
;This is a really important function, possibly one of the most important ones. This just evaluates everything.
;A lot of the test cases in the book and from Professor Troeger use this for test cases.

;pre: e is an expression that will be evaluated
;post: returns the evaluated value of e 

#| ;fix this proof
Proof:

the function directly calls (value e) = (meaning e '())
'() is the empty environment
meaning is correct (refer to 1.5)
Therefore: 
   ∀e. (value e) = ⟦e⟧_{∅}
|#

(define (value e)
  (meaning e '()))
;===========================================================================================================




;So this was a main reason why our code was not working. In TLS, it gives us initial-table. However, if we carefully
;read it, it says that this should never be used really. So this is just like a fall back and gives an error. 
(define (initial-table name)
  (error "Unbound identifier" name))



;===========================================================================================================
; This is the build function. It creates entry and validates that the names list has no dupes and
; the names list and values list are the same length. And then it returns the entry.
;===========================================================================================================

;;pre: takes two arguments, s1 and s2 which can be any valid Scheme values
;;post: returns a list of two elements, s1 is first and then s2 is second
(define build
  (lambda (s1 s2)
    (cons s1 (cons s2 '()))))


;Testing the function
; (build '(x y z) '(1 2 3))             ;returns ((x y z) (1 2 3))
; (build '((a . 1) (b . 2)) '((x . 9))) ;(((a . 1) (b . 2)) ((x . 9)))
; (build '(a (b c)) (build '(x) '(1)))  ;((a (b c)) ((x) (1)))



;;pre: takes two arguments, a list of names as first. and second is a list of the values associated
;;post: returns a new environment entry
(define new-entry build)



;===========================================================================================================
; This is the lookup-in-entry function. Accompanied with it is the lookup-in-entry-helper.
;===========================================================================================================
#|
For this proof, we will use proof by induction
;pre and post are down below

;Proof
;Base Case: When names list is empty, call the function entry-f
;IH: Assume (lookup-in-entry name (cdr entry) entry-f) works correctly for smaller lists

;IS: If (car names) matches the target: it will return (car values) 
; if this is not the case then the recursion step will commence. Recurs on (cdr names) and (cdr values)
;By IH, this will either find the name or call entry-f
;Therefore, lookup-in-entry correctly searches through name-value pairs.

|#



;pre: takes three arguments. name (the symbol to look up), entry(a list where we essentially do the searching), entry-f(error message).
;post: if name is found in the list, it returns the corresponding value. if not found, it returns the error message.
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
; (lookup-in-entry 'x entry (lambda (name) 'not-found-in-entry))                   ;returns 1
; (lookup-in-entry 'a entry (lambda (name) 'not-found-in-entry))                   ;returns not-found-in-entry
; (lookup-in-entry 'h2 '((h1 h2 h3) (ar luka lebron)) (lambda (name) 'not-found))  ;returns luka





;===========================================================================================================
; This is the lookup-in-table function. 
;===========================================================================================================
;pre: takes three arguments, name (what we are looking for), table (list of entries), and table-f (an error message if name is not found)
;;post: returns the value associated with name if it is found in table. if it does not exist, calls the table-f function.

#|
This is the proof for lookup-in-table
For this proof, we will use structural induction

;Proof:
Base Case:when tables is null, call the function table-f

IH: Assume (lookup-in-table name (cdr table) table-f) works correctly
IS: the function Tries (lookup-in-entry) on (car table)
If it is not found, we will recur on (cdr table)
By IH, this will search the remaining values correctly

Therefore, lookup-in-table works correctly.
|#

(define (lookup-in-table name table table-f)
   (cond
     ((null? table)(table-f name))
     (else
      (lookup-in-entry name (car table)
                       (lambda (name) (lookup-in-table name (cdr table) table-f))))))

;Testing the function
; (define table '(((entree dessert)
;                (spaghetti spumoni))
;               ((appetizer entree beverage)
;                (food tastes good))))

; (lookup-in-table 'entree table (lambda (name) 'not-found))    ;returns spaghetti
; (lookup-in-table 'dessert table (lambda (name) 'not-found))   ;returns spumoni
; (lookup-in-table 'appetizer table (lambda (name) 'not-found)) ;returns food
; (lookup-in-table 'snacks table (lambda (name) 'not-found))    ;returns not-found

; (define complex-table 
;   '(((alpha beta gamma)
;     (1 2 3))
;    ((delta epsilon zeta)
;     (4 5 (nested list)))
;    ((theta iota kappa)
;     ((deep nested) 8 9))))

; (lookup-in-table 'gamma complex-table (lambda (name) 'not-found))   ;returns 3
; (lookup-in-table 'zeta complex-table (lambda (name) 'not-found))    ;returns (nested list)
; (lookup-in-table 'theta complex-table (lambda (name) 'not-found))   ;returns (deep nested)
; (lookup-in-table 'lambda complex-table (lambda (name) 'not-found))  ;returns not-found






;===========================================================================================================
; TLS FUNCTIONS
; In TLS, it asks a crucial question, "How can we build an entry from a set of names and a list of values?"
; It then proceeds to tell us that we should try and build our examples with the function of
; (define new-entry build). And this is ultimately saying new-entry = build. So we need to make a build function.
;===========================================================================================================





;===========================================================================================================
; This is the check-set function. It checks whether or not the list has duplicates.
; Sets cannot have duplicates.
;===========================================================================================================

;pre: list1 is a list
;post: returns #t if list1 is a set and #f if it is not a set
(define (check-set list1)
  (cond
    ((null? list1) #t)
    ((member (car list1) (cdr list1)) #f)
    (else
     (check-set (cdr list1)))))

;Testing the function
; (check-set '())                                  ;returns #t
; (check-set '(1 2 3 4))                           ;returns #t
; (check-set '((lambda (x) x) (lambda (x) x)))     ;returns #f
; (check-set '(1 2 (lambda (x) x) 3))              ;returns #t  
; (check-set '(1 2 (lambda (x) x) (lambda (y) y))) ;returns #t





;===========================================================================================================
; This is the check-equal-len-list function. It checks whether two lists are of equal length. 
;===========================================================================================================

;pre: list1 and list2 are lists
;post: returns #t or #f based on if the lists are of equal length or not
(define (check-equal-len-list list1 list2)
  (cond
    ((and (null? list1) (null? list2)) #t)
    ((or (null? list1) (null? list2)) #f)
    (else
     (check-equal-len-list (cdr list1) (cdr list2)))))

;Testing the function
; (check-equal-len-list '() '(1 2 3))                                ;returns #f
; (check-equal-len-list '() '())                                     ;returns #t
; (check-equal-len-list '(1 2 (lambda (x) x)) '(a b (lambda (y) y))) ;returns #t
          





;===========================================================================================================
; Action Functions
; In chapter 10 of TLS, we once again meet the use of value. And value is the function that returns
; the natural value of expressions. After that, we then get introduced to the different action functions
; There are different types: *const, *quote, *identifier, *lambda, *cond, and *application. And to represent
; we use action functions. We have atom-to-action, expression-to-action, and list-to-action. 
;===========================================================================================================

;pre: takes one argument. fun (can be any Scheme value)
;post: returns #t if fun is a pair whose first element is the symbol 'primitive and #f otherwise
(define (primitive? fun)
  (and (pair? fun) (eq? (first fun) 'primitive)))

;Testing the function
; (primitive? '(primitive +))                         ;returns #t
; (primitive? '(primitive car))                       ;returns #t 
; (primitive? 'primitive)                             ;returns #f     
; (primitive? '(((primitive list)) (primitive cons))) ;returns #f
; (primitive? '(((primitive /)) extra))               ;returns #f




;pre: takes one argument. fun (can be any Scheme value)
;post: returns #t if fun is a pair whose first element is the symbol 'non-primitive and #f otherwise
(define (non-primitive? fun)
  (and (pair? fun) (eq? (first fun) 'non-primitive)))

;Testing the function
; (non-primitive? '(primitive +))                         ;returns #f
; (non-primitive? '(primitive car))                       ;returns #f 
; (non-primitive? 'primitive)                             ;returns #f     
; (non-primitive? '(((primitive list)) (primitive cons))) ;returns #f
; (non-primitive? '(non-primitive (lambda (x) x)))        ;returns #t 



;Action for constants
(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))

;Testing the function
; (*const 12 'testcase)
; (*const 'cons 'testcase)
; (*const '(lambda (x) x) 'testcase)



;Action for quote
(define (*quote e table)
  (text-of e))

;Testing the function
; (*quote '(1 2 3) 'dummy)        ;returns 2
; (*quote '(lambda (x) x) 'dummy) ;returns (x)



;Action for identifier
(define (*identifier e table)
  (lookup-in-table e table initial-table))


;Action for lambda
(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e))))


;Action for cond
(define (*cond e table)
  (evcon (cond-lines-of e) table))



;pre: takes two arguments. lines is a list of cond clauses. table is the current environment
;post: evaluates and returns the result of the first valid clause action.

#| ; fix this proof
Proof for Evcon using Structural Induction
Base Case: idk!

IH:Assume (evcon (cdr lines) table) evaluates remaining clauses correctly

Inductive Step:
Evaluates (question-of (car lines)) using meaning
If true/else: returns (answer-of (car lines))
Else: recurs on (cdr lines)
By IH, this handles the remaining clauses properly
This shows evcon correctly implements the cond semantics.
|#

(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))



;Takes a list of arguments and a table, and then returns a list composed of the meaning
;of each argument.
;pre: takes two parameters. arguments is what needs to be evaluated. table is the current environment
;post: returns a list of the evaluated arguments

#| ; this also need to be fixed
Proof for evlis using
structural induction
Base case: when args is null, it returns correct value ; this is wrong

IH: Assume (evlis (cdr args) table) evaluates remaining args correctly

IS: the function Evaluates (car args) using meaning function
it then cons onto recursive call with (cdr args)
By IH, (cdr args) evaluates correctly

Therefore, evlis properly evaluates argument lists

|#
(define (evlis args table)
  (if (null? args)
      '()
      (cons (meaning (car args) table) (evlis (cdr args) table))))


;Action for application
(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))




; This is the TLS apply primitive. It essentially handles all of the primitives in the chapter
; where the interpreter was introduced.

;pre: this takes two arguments. name (symbol representing the primitive op name). vals (a list of arguments).
;post: applies the operation and then returns the result. if it is not recognized, we return an error.

#| ; adjust the language
Proof for tls-apply-primitive

Case Analysis Proof:
1. +: Applies R5RS addition 
2. cons: Creates pair 
3. car: Returns head of list (with error check) 
4. cdr: Returns tail 
5. null?: Checks emptiness 
6. eq?: Tests equality 
7. Default: Raises error 

Therefore all primitives are correctly implemented.
|#
(define (tls-apply-primitive name vals)
  (cond
    ((eq? name '+) (apply + vals))
    ((eq? name 'cons) (cons (first vals) (second vals)))
    ((eq? name 'car)
     (if (null? vals)
     (error "primitive 'car' called with no arguments" name)
     (car (first vals))))
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

;Testing the function
; (tls-apply-primitive '+ '(1 2 3))      ;6
; (tls-apply-primitive 'cons '(1 (2 3))) ;(1 2 3)
; (tls-apply-primitive 'car '((1 2 3)))  ;1
; (tls-apply-primitive 'cdr '((1 2 3)))  ;(2 3)
; (tls-apply-primitive 'null? '(()))     ;#t
; (tls-apply-primitive 'unknown-op '(1 2)) ;error: unknown primitive unknown-op
; (tls-apply-primitive 'car '())           ;ERROR: primitive 'car' called with no arguments car




;In TLS, the function was originally called "apply", but Scheme R5RS already has its built in apply,
;so I made another one specifically called tls-apply.

;pre: takes two arguments. fun (value expected to be prim or non-prim. vals is a list of argument values
;post: if fun is primitive, it applies tls-apply-primitive and returns. if non-primitive, applies closure and returns.
;      else error message.

#| ;also needs to be fixed
Proof for TLS-Apply

Proof by cases:
1. primitive?: Delegates to tls-apply-primitive 
2. non-primitive?: Delegates to tls-apply-closure 
3. Else: Raises "not a function" error 

Therefore, tls-apply is implememnted correctly.
|#
(define (tls-apply fun vals)
  (cond
    ((primitive? fun) (tls-apply-primitive (cadr fun) vals))
    ((non-primitive? fun) (tls-apply-closure (cadr fun) vals))
    (else (my-error "tls-apply: not a function" fun))))

;Tests for function
; (define primitive-fun '(primitive +))
; (tls-apply primitive-fun '(2 3))   ;returns 5
; (tls-apply 42 '(1 2))              ;ERROR: tls-apply: not a function 42
; (tls-apply primitive-fun '(1 10))  ;returns 11



(define :atom?
  (lambda (x)
    (cond
     ((atom? x) #t)
     ((null? x) #f)
     ((eq? (car x) 'primitive) #t)
     ((eq? (car x) 'non-primitive) #t)
     (else #f))))


;pre: closure is a list with at least three elements: saved environment, formals list, and body expression;
;      vals is a list of argument values.
;post: extends saved environment with formals bound to vals, evaluates body in the new environment, and returns the result.

#|
Proof for Tls-apply-closure

Proof:
1. Unpacks (table formals body) from closure
2. Creates new env via (extend-table formals vals table)
3. Evaluates body in new env via meaning 

Hence, closures are applied correctly.
|#
(define (tls-apply-closure closure vals)
  (let*
      ((saved (first closure))
       (formals (second closure))
       (body (third  closure))
       (new-env (extend-table formals vals saved)))
    (meaning body new-env)))
  


;===========================================================================================================
; This is the atom-to-action function. This was already given to us in TLS chapter 10. The purpose of this is
; to decide how to evaluate an expression. And returns the correct "action". 
;===========================================================================================================

; pre: e is any Scheme value.
; post: returns *const if e is a constant atom. else returns *identifier.
(define (atom-to-action e)
  (cond
    ((const-atom? e) *const)
    (else *identifier)))

;Testing the function
; (atom-to-action 5)                                   ;const
; (atom-to-action 'list)                               ;identifier
; (atom-to-action 'lambda)                             ;identifier
; (atom-to-action '(lambda (x) (lambda (y) (+ x y))))  ;identifier
(newline)




;===========================================================================================================
; This is the list-to-action function. This was also given in TLS. The purpose of this is to handle expressions
; that are not atoms, hence why we have quote, lambda, and cond as a comparison for our eq? and return it.
; Also deals with *application. 
;===========================================================================================================

; pre: e is a non-empty list.
; post: returns *quote if (car e) is 'quote; *lambda if 'lambda; *cond if 'cond; 
;       else *application.
(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote)  *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond)   *cond)
       (else *application)))
    (else *application)))

;Testing the function
; (list-to-action '(lambda (x) ((lambda (y) (+ x y)) 5)))               ;*lambda
; (list-to-action '(lambda (x) (lambda (y) (lambda (z) (+ x y z)))))    ;*lambda
; (list-to-action '((lambda (x) ((lambda (y) (* x y)) 2)) 3))           ;*application
; (list-to-action '((lambda (x) (lambda (y) (x y))) (lambda (z) z)))    ;*application
; (list-to-action '(cond ((> x 0) x) ((< x 0) (- x)) (else 0)))         ;*cond
(newline)



;===========================================================================================================
; This is the expression-to-action function. This was also given in TLS. The purpose of this can be thought of
; as the main function, it calls both of the two previous functions given what we have inputted. And then the other
; two can be considered helper functions that do all of the work. 
;===========================================================================================================

; pre: e is any Scheme value.
; post: returns atom-to-action e if e is an atom; otherwise returns list-to-action e.
(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))

;Testing the function
; (expression-to-action '(quote hello))                           ;#<procedure:*quote>
; (expression-to-action '(quote (1 2 3)))                         ;#<procedure:*quote>
; (expression-to-action '(lambda (x) (lambda (y) (+ x y))))       ;#<procedure:*lambda>
; (expression-to-action '((lambda (x) (lambda (y) (+ x y))) 3))   ;#<procedure:*application>
; (expression-to-action '(if (zero? x) 0 (add1 x)))               ;#<procedure:*application>

; ((expression-to-action '(lambda (x) (+ x 1))) '(lambda (x) (+ x 1)) '())
; (non-primitive (() (x) (+ x 1)))

; ((expression-to-action '(lambda (x) x)) '(lambda (x) x) initial-table)
; (non-primitive (#<procedure:initial-table> (x) x))

; ((expression-to-action '(lambda (x y) (+ x y))) '(lambda (x y) (+ x y)) initial-table)
; returns (non-primitive (#<procedure:initial-table> (x y) (+ x y)))

; ((expression-to-action '(lambda (x) (lambda (y) (+ x y)))) '(lambda (x) (lambda (y) (+ x y))) initial-table)
; returns (non-primitive (#<procedure:initial-table> (x) (lambda (y) (+ x y))))
(newline)
(newline)






   



;===========================================================================================================
; Error Functions
; In chapter 10 of TLS, we get introduced to parameters within our function that ends in -f. For example, we
; have set-f, entry-f, table-f, etc, etc. These are known as error functions. Because we don't want to actually
; write an else clause and then an error message.
;===========================================================================================================

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








;TEST CASES GIVEN BY PROFESSOR. DO NOT COMMENT THESE OUT.
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
