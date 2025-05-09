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


;4/12-Kenneth(Comments Below)
; 1.1 is basicly a translation of TLS from TLS language into R5RS. I do notice that some functions from the book are repeated so i think the outline
; for the interpreter would be to get the simple functions and helpers out of the way first, that way we can keep refering to them and avoid redundent code.
;Initially i wll focus on just pure translation and then after everything is translated I will focus on connecting the important components

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

;4/14-Kenneth(Commments Below)
;I implememnted most of TLS straight from the book, some of the functions still need to be linked.Most of the test cases that i did work with the function
; on its own, however there are certain functions that connect that have some logical errors to them, so we will hopfully work on fixing that. Since TLS
;had some repeated functions that did diffrent things we still have to clean and fix that so that each function can past every test case.

;4/14-Alexis(Comments Below)
; I reviewed the code Kenneth implemented and fixed some errors, and added some of the basic functions from the book TLS. 
; Kenneth explained the outline and how some of the functions are repeated and some of the logic in TLS is flawed.


; 4/16/25 - Hamim (Comments Below)
; Today was just completing the build function in TLS, what this function does is that it returns an entry if it satisfies two conditions. The
; first condition being that the names list does not contain duplicates, aka is a set. And the second condition being that the values list and
; names list are of equal length. Both of the conditions have their own function, check-set and check-equal-len-list. Kenneth had already begun
; a basic outline of it, I just added onto it and finalized it. Alexis and myself were working on the pre and post conditions as well.


; 4/17/25 - Hamim (Comments Below)
;Action functions.

;4/19-Kenneth (Comments Below)

;Started on the Syntax checker for TLS.Since we have a lot of functions for TLS I decided to have two refrences, conditons and special conditions
;Conditions will be all the operations that can be easily checked such as some of the built in operations and some primitives. Since some
;operations will be more complex like lambada where we will probably have to reccur to check all the other operations inside it we can always refer
;to the condtions to show if the arguments inside them follow the correct format.


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


;4/29-Kenneth(Comments Below)
;After My inital layout of the syntax checker i realized that some of the Design was not correct. We dont really need a special-checker since
;each of the functions like lambda,cond,if ect does its own unique thing so refering to that would be redundant.I'm still not finished with it but most of the
;basic operations are done.The specific TLS functions still need to be checked and also need to work on showing specific
;error messages instead of just outputting false.

;4/29-Alexis (Comments Below)
; I realized how complicated Cond is when it comes to this since I will need the helper functions made for expression. 
; Although And and other functions were made, I only used syntax-checker we made.
; I also added specs to my previous function kenneth and I made. 
; And finished more basic functions.

;4/30/25 - Hamim (Comments Below)
;Cleaning up code, making sure test cases all run. In order to make the output look nicer, I added two (newline) so it is easier to see the output and what
;section of code corresponds to what.


;4/30/25 - Alexis (Comments Below)
; I implemented some finishing touches to 1.1 for we can present the code to the professor tomorrow. 
; I also cleaned up 1.2 file and added some specs we missed. 
; Fixed some errors as well.


; Now how do we approach this? In chapter 10 of the book we have some functions written completely and we just need to convert that to R5RS,
; and some do not. Kenneth already began to create the basic helper functions and write the functions in Scheme (4/14/25). We started off by
; first creating the basic helper functions, the ones that are in the chapter and commonly used in TLS and then we went through the list one
; by one and made the functions. 


;----------------------------------------------------------------------------------------------------
;1.3
;------------------------------------------------------------------------------------------------------


;; 1.3 After giving a specification for the environment subsystem of TLS, prove that your implementation
;;     satisfies this specification.  Then change the representation of environemnts to use lists of
;;     bindings rather than the names-values pairs shown in the text, and show that the altered
;;     representation both satisfies your specification and works with the rest of the interpreter.


;------------------------------------------------------------------------------------------------
;Specs of the  current Enviorment
;----------------------------------------------------------------------------------------------------
;So first we must give a spec for the enviorment subsystem in TLS and then we have to prove that
; our implementation fufills that specification.


;In TLS the enviorment refers to the table, which is a list of entires, and each entry consistes of varible bindinds
;which are repsented as a key value pair like:
;(( x y z)( 1 2 3))
;The first list contains the names of the varible and the second one the values.

;They key functions in the Current TLS are:
;-empty-env: returns an empty tavle ()
;-build : constructs an entry froma  list of names and a list of values
;-extend-table: preappends a new entry to the enviorment
;-lookup in entry: searches for a name in a single entry
;lookup-in-table:reccursivly searchs throigh the table for a binding




;-----------------------------------------------------------------------------------------------
;Function conditions
;----------------------------------------------------------------------------------------------

;empty-env
;Pre condtion: none since
;Post condtion: returns '()

;build
;Precondtion: names is a list of unique symbols which has the same len as values
;Post condtion: returns a pair of (names.values)

;extend-table
;Precondtion: entry is produced by build,the table is a list of entries
;Post condtion: returns a new table with the entry prepended

;Lookup-in-entry
;Precondtion:entry is a pair(names . values)
;Post condtion: returns the value at a postion of name in names,else calls entry-f

;lookup-in-table
;precondition:table is a list of entries
;Postcondtion: searces each entry using lookup-in-entry, else it calls table-f
;-----------------------------------------------------------------------------------------------
;PROOFS on our functions
;---------------------------------------------------------------------------------------------

;Proof empty env:
;Returns '(). Any lookup falls through and calls table-f, which is the correct behavior for an unbound varible

;Proof  Build
;Constructs an entry by pairing names and values. The invarient we mantain is list-ref = name i =n
; which means that the list-ref values i is bound to n

;Proof lookup-in-entry
;Base case:the length of our list is empty so we execute (entry-f name) since no correct binding exists.

;Inductive Hyptothesis: assume the propeties holds for rest-ns

;inductive step: if (car names) mathces the query then we return (car values) since they are bounded to one another
;otherwise we reccur on (cdr names) and (cdr values) ensuring that the name value pairing remains true.


;Proof lookup-in-table
;Base case: the table returns empty and calls the function (table-f s)

;Inductive hypthesis: Assume that property holds for rest-table

;inductive step: Do a check on (car table) if entry contains name, return value
;else we reccur on (cdr table)


;-----------------------------------------------------------------------------------------------
;name, value pairs ->>>>>> List-of-Bindings
;-----------------------------------------------------------------------------------------------


;changing the representation of environemnts to use lists of bindings rather than the names-values pairs
;SO far our implementation consists of name value pairs in the enviorment tables,
; previously our enviorment tables :
;(( x y z)( 1 2 3))

;We want to change that into

;((x.1)(y.2)(z.3))



;In order to do this we would have to implement some of the enviorment attributes
;that we learned about in eopl.

;In eopl there are 4 important function enviormiorments
;We have empty-env,extend-env,extend-env*, and apply env

;------------------------------------------------------------------------------------------------
;The New Enviorment
;------------------------------------------------------------------------------------------------
( define empty-env '())


;Proofs on The new enviorment

;Precondition: env is a list of (name . val) bindings.

;Postcondition: Returns a new environment with (name val) added to the front.

(define (extend-env name val env) 
  (cons (list name val) env))

;Base case: If names is null then vals should also be null so program returns the env

;Inductive hypothesis: Assume that for the lists rest-names and rest-vals,the enviorment correctly
;extends for all other bindings from rest-names to rest-vals

;Inductive step:we let our names be (cons name rest-names) and our values be (cons val rest-vals)
;this will result in our extend*env looking like extend*env rest-names rest-vals(extend-env name val env)
;Via the defention of our IH our extend*env should add all the bindings from rest-names and rest-vals
;Via the proof from extend-env our env(car names)(car vals) should be added to the front.
;Therfore the full call builds and enviorment with the bindings from names and vals.

(define (extend-env* names vals env)
  (if (null? names)
      env
      (extend-env* (cdr names)
                   (cdr vals)
                   (extend-env (car names) (car vals) env))))

;Base case:The lookup is unsucsesfull and returns an error
;Inductive hypothesis:Assume for the tail rest-env,(apply-env rest-env name) returns the value for the name
;Inductive step: our env =( cons binding rest-env)
;if the name matches the cadr of env then we return it with the correct value, if we dont then we keep on reccuring
;Via the IH our function returns the correct result until either the value is found or we run into an error.
(define(apply-env env name)
  (cond ((null? env)
         (error 'apply env(format "unbound identifier: ~a" name))) 
        ((eq? name (car(car env)))
         (cadr(car env)))
        (else
         (apply-env(cdr env) name))))


;-------------------------------------------------------------------------------------------------
;Transforming the rest of the code for compatibility
;------------------------------------------------------------------------------------------------

;Since we defined a new enviorment we have to change some of the functions in order to ensure compatibility
; Old version used:
; (define (extend-table formals vals table)
;   (cons (build formals vals) table))

;New version:
(define (extend-table formals vals table)
  (extend-env* formals vals table))

;Old version used
; (define (*identifier e table)
;   (lookup-in-table e table initial-table))

;New Version:(in the bottom of the code)
;( defined in code)(Put line of it once done)
;(define (*identifier e table)
  ;(apply-env table e))

;------------------------------------------------------------------------------------------------
;Overall analysis and conclusion
;-----------------------------------------------------------------------------------------------

;How did alterning our lookup enviorment and enviorment in general ensure that our enviorments represent list bindings?

;Initally with our pure TLS translation our entry was two parallel lists with a name and value relatshonship.
;Lookup table would grab an entry then would find the postion of the name and return the matching value.
;  our  initial table consisted of a list of entries which relied on two diffrent lists.

;After the implementation of a new enviorment our program followed the binding model which eliminates
; the need for the name value relatshonship making the table a list of bindings
;This required all our identifiers to go through apply-env which susbstituted for lookup-in-entry and lookup-in-table.
;Once that is updated we then had to change extend-table to match our new enviorment and that required the use of extend-env* which
;instead of forming a name value pair, it pushed bindings for every actual pair so instead of (x y z)( 1 2 3) extend-env* would
;do ( x 1), ( y 2), ( z 3)

;----------------------------------------------------------------------------------------------------------------------------
;Tests
;-----------------------------------------------------------------------------------------------------------------------------

(define 1.3-env
  (extend-env* '(x y)
               '(1 2)
               (extend-env* '(z)
                            '(3)
                            empty-env)))

(apply-env 1.3-env 'x) ; => 1
(apply-env 1.3-env 'y) ; => 2
(apply-env 1.3-env 'z) ; => 3
;(apply-env test-env 'a) ; => error: unbound identifier: a

(define env1
  (extend-env* '(a b c) '(1 2 3) empty-env))

(apply-env env1 'a) ; => 1
(apply-env env1 'b) ; => 2
(apply-env env1 'c) ; => 3


(define env3
  (extend-env* '(x y) '(42 43)
    (extend-env* '(p q) '(5 6)
      (extend-env 'r 100 empty-env))))

(apply-env env3 'x) ; => 42
(apply-env env3 'p) ; => 5
(apply-env env3 'r) ; => 100
;(apply-env env3 'z) ; => error: unbound identifier



;--------------------------------------------------------------------------------------------------
;1.4 Closures and Lexical Scope in TLS
;---------------------------------------------------------------------------------------------------------
;; Question: Research closures and lexical scope, and prove that your
;; implementation of TLS supports these features correctly.
;; Provide definitions, structural insights, and use induction to justify correctness.

;----------------------------------------------------------------------------------------------------------
;Quick Backround: Lexical Vs Dynamic Scoping
;--------------------------------------------------------------------------------------------------------
;1.4 of the project is asking us to research closure and lexical scope and prove that our implementation
; of TLS implements them correctly.


;The first part of the assigment is for backround and asking us to research what exactly lexical scoping is
; our findings and research of lexical scope, along the way we decided to do a comparison between Dynamic and Lexical scoping.



;Dynamic scoping is looked at like a  stack like structure where the varible pushed is whats first in the scope/ innermost function.So the most recent binding varible
;is what is used even if the varible was defined in a diffrent scope.So the most recent varible determines the value of it at run time regardless of where
; the function was originally defined.

;Lexical scoping is when we determine the varible at compile time rather thean run time. Instead of a stack the varible
; we refer to is based on our static structure of the code.A varible is bound by the closest encolosing lambda, expression at the time the function
; is defined, not a the time it is called

;What exactly is lexical scoping?
;An items lexical scope is the place in which it was created.
;Some varibles can be delacred within a specific scope and are only accesible withing that reigon.
;Lexical Scope refers to the ability of a function scope to acess varibles from its parent scope so
; when there is a lexical scope innermost, inner and outermost functions may access all the varibles from
;their parent scopes all the way up to the global scope.
;However one key detail is that a scope cannot acess varibles from functions defined inside of it,
;so the childs function is lexically bound to the parents function.


;Basic example to show the difference between dynamic and lexical scoping

; (define y 10)
; (define (h) y)
; (define (ad) (let ((y 20)) (h)))

;In lexical scoping ad would return 10 because h was defined in an enviorment
;In dynamic scoping it would return 20 because h is called inside of the scope of y=20.


;--------------------------------------------------------------------------------------------------------
;Key concepts
;--------------------------------------------------------------------------------------------------------


;Now that we've explained the key differences between lexical and dynamic scoping we are going to go more in depth in explaining lexical scope.

;Important defenitons:

;Bound-Occurance: a bound occurance is when a varible sits inside the scope that it introduces it in.Bound has a binding right there
;Free occurance:  a varible that is not introduced locally and not bound by an local bindings. Free to look outside the local scope
;Unbound occurance: a varible that is undefined. Unbound is owned by no one.

;What is a closure?

;a closure is the run time value profuced when a function is created inside some lexical enviorment
;It contains
;1. The functions body
;2. An environment that captures the values of free variables at definition time


; ------------------------------------------------------------------------------
   ; TLS Implementation of Lexical Scope and Closures
; ------------------------------------------------------------------------------

;A lambda expression is converted into a closure by capturing the current enviorment.
;
;(define (*lambda e table)
 ; (build 'non-primitive (cons table (cdr e))))


;;(define (tls-apply-closure closure vals)
  ;(let*
      ;((saved (first closure))
      ; (formals (second closure))
       ;(body (third  closure))
       ;(new-env (extend-table formals vals saved)))
  ;  (meaning body new-env)))



;(define (*identifier e table) 
;  (apply-env table e) )


; These code snippits demonstrate lexical scoping:
; - When a lambda is created, the current table is captured into the closure.
; - When called, a new environment is built over the saved table.
; - Variable lookup always uses the environment stored in the closure.


; ------------------------------------------------------------------------------
;  Structural Induction Argument for Correctness
; ------------------------------------------------------------------------------


;How does our code demonstrate that it is lexically scoped?

;From the defneition we provided above and the snipiets of code bellow is what we will use to prove that
;our implementation of TLS implements lexical scoping.

;Structure:
;Creating the lambda captures the current enviorment.
;The function applicaiton extends the captured enviorment with new bindings.
;Evaluation used the extended enviorment via 'apply' env

;Base case:
; when-Expression is a literal no lookup ocurs
;When expression is a variable, it gets evaluated using apply-env which searches the stored enviorment

;Indcutive Hyptothesis: all the subexpressions respect Lexical scoping

;When evaluating the lambda body
;- the bodu uses a closures enviorment and not the callers
;- Any free varibles in the body refere to the bindings in the saved or above
;Therfore all the varibles are resolved lexically based on where the function was defined in the code
; and not when its called.

;------------------------------------------------------------------------------------
;Demonstration
;------------------------------------------------------------------------------------

; This function creates a closure over x:




 ((lambda (x)
   ((lambda (f)
      ((lambda (x) (f)) 20))
    (lambda () x))) ; ← at this point x is bound
 10)

;--------------------------------------------------------------------------------




;---------------------------------------------------------------------------------
;1.3 and 1.4 Relatshonship
;--------------------------------------------------------------------------------

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
  (extend-env* formals vals table))

;This is a really important function, possibly one of the most important ones. This just evaluates everything.
;A lot of the test cases in the book and from Professor Troeger use this for test cases.
;(define (value e)
  ;(meaning e '())) 


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



;(define (lookup-in-entry name entry entry-f) 
 ; (let loop
   ; ((names (first entry))
     ;(values (second entry)))
    
    ;(cond
     ; ((null? names) (entry-f name))
     ; ((eq? (car names) name) (car values)) 
      ;(else
       ;(loop (cdr names) (cdr values))))))

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
;(define (lookup-in-table name table table-f)
  ; (cond
     ;((null? table)(table-f name))
     ;(else
      ;(lookup-in-entry name (car table)
                       ;(lambda (name) (lookup-in-table name (cdr table) table-f))))))
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
;(define (*identifier e table)
  ;(lookup-in-table e table initial-table))
;Changed after 1.3 to
(define (*identifier e table)
  (apply-env table e) )     


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











;1.7 Y-combinator TLS-REC
;------------------------------------------------------------------------------------------------


;1.7 ;NOT COMPATIBLE WITH TLS YET,, FIXES NEEDED

;1.7 asks to equip our TLS interperter with the Y-Combinator

;Task:
;; 1.7 Drawing on Chapter 9 of The Little Schemer, equip your TLS with recursion to form TLS-REC, using the Y-combinator.
;;     Research Y-combinators, and prove that the implementation you use actually implements a Y-combinator.
;;     Explain, in detail, how the Y-combinator implements recursion.  Include interesting examples
;;     of recursive programs written TLS-REC.


;Before equiping our TLS with the Y combinator, we have to ask, what does the Y-Combinator even do??
;After researching it thorughly we came to the conclusion that Y-combinator solves reccursion
;without any self refernce. This is a bit mind blowing because it seems like it shouldnt be possible.

;Throught this semester and in other classes and in prepearing for interviews we learned that jumping straight into code
;is a bad idea since you are just throwing things onto the wall and hoping that it sticks, so because of this
; we deleved a little bit into lambda calculus first to figure out what all of this means.

;Lambda calculus is a very unique tool that can be used in any programing language as its all logic that
;can be applied and executed anywhere

;We started of simple looking at basic lambda calculus examples like

; True=λx.λy x
; False=λx.λy y
;In our case the lambdas serve as our inputs, where x and y are the said inputs and we output the first value
;which would signify true, if we take y then that would siginfy false.

;This is cool and all but how does lambda calculus even do anything??
;Lambda calculus uses substitution to calculate its values

;Ex:(λx.x+1)
;^ takes x as an input and executes x+1
;(λx.x+2)22
; in this case we use substitution where the outside value takes the place of x,
; so our output would be 22+2 giving us 24.

;This is the basic "Syntax" when it comes to the lambda calculus, the next thing we went over was
;loops in lambda calculus

;reccursion and loops ultimilty do the same job when it comes to solving a problem, some of the key differnces
;being the difference in time and space complexity.

;in lambda calculus a loop is defenined by using
;(λx.xx).(λx.xx)
;This a bit confusing to look at, at first. We see the input being of the langauge x and
;have two of them and the parameters being the input function itself.
;In reality this is simple, we just treat the parameter like an normal input
; giving us
;λx.(λx.xx)(λx.xx)
; this process would keep repeating until we reach a stopping condition, so thats the basics of a loop in lambda calcus!
; its a function that takes itself as an input how many times are needed.

;after figuring out the looping aspect of lambda-calculus, the y-combinator operation is not much diffrent
;The Y combinator states: λf(λx.f(xx))(λx.f(xx))
;where λx is the input language, and our first function is what is serving as the input and the parameter
;being the value that will be susbsituted into the input language.

;This formula is basicly lambda calculus way of imitating reccursion, its not reccursive just implies it

;Quick proof on how this implies reccursion

;Given the defenition Y=λf(λx.f(xx))(λx.f(xx))
;so given the defention Y we want to show that Y(F)= F(Y F)

;all we really have to  do is expand Y
;so given the defenition  Y=≈(λx.f(xx))(λx.f(xx))F
;once we subsititue we get (λx. F (x x)) (λx. F (x x))
;then this implies F ((λx. F (x x)) (λx. F (x x)))
; so after plugging in we got back to where we started so it shows that Y F= F( Y F)

;Formal proof:LATER

;okay now after defining the defention and proving the code, how would we implement the Y-Combinator in TLS
;Before diving into the design idea, when we were first focusing on translating we ran into some issues
; our intial apporach made us give this as the implementation:

;(define Y
  ;(lambda (f)
   ; ((lambda (x) (f (x x)))
     ;(lambda (x) (f (x x))))))

;At initial glance this looks fine we define Y as the function which serves its purpose as a defention
;we then make the lambda,lambda(f) which serves as our outside function λf, then our inside functions
;serve as our (λx.f(xx))(λx.f(xx)).

;if that direct translation is good, then what is the problem?

;This took some research and what we found is that it has to do with schemes evaluation
;In our case ( f(x x)) is evaluated imediatlly meaning that we call the parameter into the function, but it keeps calling itself an infinite amount of times
;due to it being a value and fufilling the closure properties. So we keep calling ( f(xx)) (f(x x)) an infinite amunt of times without f actually being executed
;so it keeps calling but with no result.

; to correct this we created a sepreate function with similar properties but with the edge case of infinite looping covered

;Original Design idea:given our already defined function in lambda calculus (λx.f(xx))(λx.f(xx)), our goal is to convert this Y-combinator into TLS and intertwine our interpeter
; to TLS.We know that the Y-Combinator just implies reccursion meaning that it has no traditional reccursive call backs.So because of this we know that our initial fucntion defention will never be called
; it would just be there to give it a name. the second part of the Y-combionator consists of λx, which is just the lambda defnetion of the function so we should create the lambada function
;which will take an input and a paramater which should be duplicated, meaning that it should be the same as the input. Now our body should consist of the traditional (λx.f(xx))(λx.f(xx)).
;meaning we form two lmabdas looking like (lambda(x) (f x x)),(lambda(x) (f x x)).

;Adding on to the design idea
;After research our skeleton has the right structure but in order to prevent infinite calls we have to implement something that can capture the elements and execute correctly.
; since our original guess code dosent really take into consederation the susbstitution property of lambda calculus.

;In The little schemer book this is defined as
;( define Y
     ;(lambda(le)
        ;((lambda(f) ( f f))
         ;(lambda(f)
            ;(le(lambda( x(( f f ) x))))))

;However we optimized it a little bit and came up with this code


(define Y   ;Global name
  (lambda (F)  ;Y expects one argument
    ((lambda (x)  ;Creates the first of two closures which will be applied to each other
       (F (lambda (v) ((x x) v))))     ; lambda(v) makes the argument a value immedeiatly preventing the infinite reccursion
     (lambda (x)    ;duplication of y combinator which serves as our reccursion
       (F (lambda (v) ((x x) v)))))))

;our lambda(v) will serve as a closure and v will be our substitution value which will be invoked when reccuring, this is used
; so that our f(x x ) actualy call something without the inifite process of calling themselves.


;Before integrating it into our TLS we will run some basic examples to show that our implementation
;works on small scale functions

(define fact-maker ; when called this refers to the Y combinator function itself
  (lambda (self) ;This serves as our  λx/λself function expecting an input and its parameters
    (lambda (n) ;the facrotial function
      (if (zero? n) ;;;;;Basic factorial logic
          1
          (* n (self (- n 1))))))) ;Fufills y combinator by not calling itself and instead implying reccursion

(define factorial (Y fact-maker))

(factorial 0)  ; ⇒ 1
(factorial 5)  ; ⇒ 120
(factorial 10) ; ⇒ 3628800

( define sum-maker
   (lambda(self)
     (lambda(n)
       (cond
         ((= n 0)0)
         (else
          (+ n( self( - n 1)))))))) ;remeber to always refer to self, function is just there to be named

(define sumation( Y sum-maker)) ;this would make the function so Y would swallow sum-maker

(sumation 5)
(sumation 0)
(sumation 10)
(sumation 1)
(sumation 6)

(define len-list ;global name
  (lambda(self)  ; reccur on
    (lambda(lst)  ;this is the inside fucntion where all the applications go through
      (cond
        ((null? lst) 0)
        (else
         (+ 1(self (cdr lst))))))))

(define list-len( Y len-list))

(list-len '( 1 2 3 4 ))


;Okay now that we got all the defention stuff out of the way, how can this useful feature be integreated into our TLS??
;So if we refer back to 1.3, we changed the enviorment so we can simply build on top of it.
; we also have to refer to our meaning function since,

;TLS_REC_IMPLEMENTATION




(define initial-env 
  (extend-env  
   'Y
   (meaning
     '(lambda (f)
        ((lambda (x) (f (lambda (v) ((x x) v))))
         (lambda (x) (f (lambda (v) ((x x) v))))))
     empty-env)
   empty-env))



; we also have to change our value function from
;(define (value e)
  ;(meaning e '()))  to something that will accept the Y-combinator

;since we already defined our inital-env we can simply pass it to value

(define (value e)
  (meaning e initial-env))

;TESTS
;---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

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
















;-------------------------------------------------------------------------------------------------