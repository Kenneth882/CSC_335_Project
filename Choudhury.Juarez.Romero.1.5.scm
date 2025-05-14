; This is for section 1.5 of the project

;; ==================================================================================================
;1.5 After carefully identifying a standard of correctness, prove that your implementation of TLS is
;correct according to that standard.
;; ==================================================================================================



;; ===================================================================================================================
#|
So the hardest part for this section for us was to essentially understand what it means when the problem says "standard of
correctness". And how to actually prove it.
Beginning with the standard of correctness, we understand it as: what it means for our interpreter to work correctly.
This includes what it should do for a given input and proving that it behaves as expected.
|#
;; ===================================================================================================================




;; ===================================================================================================================
;;STANDARD OF CORRECTNESS FOR OUR TLS INTERPRETER:
#|
Our TLS interpreter is correct if, for every valid TLS expression, it produces the same result as R5RS Scheme, where the expression is within the subset of
Scheme supported by The Little Schemer (TLS). That means our interpreter should evaluate expressions in the same way as an R5RS interpreter, assuming pure
functional behavior and TLS-specific constraints.

1) Primitives. We wish to focus on the primitive operations. In TLS, there are primitives such as +, car, cdr, cons, null?, eq?, zero?, atom?, etc, etc
And we want these to return the same result as R5RS Scheme.

2) Functions. For lambda functions, TLS represents them as closures (formal parameters, body, environment), and we want to make sure that there
is proper binding for the parameters. We want to ensure lexical scoping. And ultimately, the correct evaluation of the body.

3) Errors. In TLS, we are introduced to things such as build-f, entry-f, etc, etc. These are just error messages that are commonly for undefined,
incorrect number of arguments, and primitive errors. And TLS widely says the error.

4) Conditionals. In TLS and Scheme, we have cond, if, and else? These should go into the correct branch and return the result associated with that branch. We
can have long conditional statements, but regardless, it should return the right answer. It's sort of like our names and values. Names is the branch and then we
return the value associated with the name. In TLS, this mimics R5RS. 

5) Atoms. We have an atom? In TLS, and we can make it in R5RS Scheme. If we have an atomic expression, it should always return itself. Meaning numbers and
Booleans should return themselves. Constants evaluate to themselves. 
|#


(define atom-to-action
  (lambda (e)
    (cond
      ((number? e) *const)
      ((eq? e #t) *const)
      ((eq? e #f) *const)
      ((eq? e 'cons) *const)
      ((eq? e 'car) *const)
      ((eq? e 'cdr) *const)
      ((eq? e 'null?) *const)
      ((eq? e 'eq?) *const)
      ((eq? e 'atom?) *const)
      ((eq? e 'zero?) *const)
      ((eq? e 'add1) *const)
      ((eq? e 'sub1) *const)
      ((eq? e 'number?) *const)
      ((eq? e '+) *const)
      ((eq? e '-) *const)
      ((eq? e '*) *const)
      ((eq? e '/) *const)
      (else *identifier))))


(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote)  *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond)   *cond)
       (else *application)))
    (else *application)))

(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))
;; expression-to-action determines which case to apply based on syntax.



(define (meaning e table)
  ((expression-to-action e) e table))

(define (value e)
  (meaning e '()))



;; ===================================================================================================================
;; PROVING THAT THE IMPLEMENTATION OF OUR TLS INTERPRETER MEETS THE STANDARD
;; ===================================================================================================================


;; ===================================================================================================================
;Let's focus on number 1, primitives. In TLS, cons, car, cdr, null, eq?, etc, etc are constants. We know this because in the atom-to-action
;function listed above, they're *const. Each primitive should be applied correctly. 

; (atom-to-action 'cons) ;#<procedure:*const>
; (atom-to-action 'eq?)  ;#<procedure:*const>
; (atom-to-action 'add1) ;#<procedure:*const>

; (value '(add1 9))          ;10
; (value '(sub1 8))          ;7
; (value '(number? 1))       ;#t
; (value '(number? 'a))      ;#f
; (value '(cons 'a '(b c)))  ;(a b c)
; Each result matches what we'd expect in TLS and R5RS Scheme for these primitives. This proves that our interpreter correctly recognizes
; these primitive symbols and applies them correctly. Keep in mind that for TLS, we don't have +, *, -, /, we need to make things like add1, sub1.

; Base Case: Each primitive is represented by a constant function returned from atom-to-action, like in lines 102-105
; IH: Assume that for all arguments k1, k2, ..., kn passed to a primitive, each ki is evaluated correctly by TLS and gives the correct value
;     expected by R5RS.
; IS: For each primitive that we have defined, we can apply it using value and then confirm with R5RS. This can be shown in lines 106-110. 
;; ===================================================================================================================


;; ===================================================================================================================
;Now let's focus on number 2, functions. In TLS, functions can be specified in a special way. Lambda expressions define functions but they are
;represented as closures. A closure has formal parameters, the body, and the environment. So for us we use expression-to-action to find a lambda
;function because it uses list-to-action too. And then by *lambda, we make the closure. And *application, applies the closure by evaluating the
;arguments, binding, and then evaluating the body. This is a complex process, so we need to make sure that it actually returns the correct answer.
; (value '((lambda (x) x) 1))                                ;1
; (value '((lambda (x) (add1 x)) 99))                        ;100
; (value '(((lambda (x) (lambda (y) (cons x y))) 'a) 'b))    ;(a . b)
; (value '((lambda (x y) (cons x (cons y '()))) 'a 'b))      ;(a b)
;Here lambda expressions are turned to closures, parameters are bounded, and the final values match with what R5RS Scheme would return.

; Base Case: A lambda expression and a primitive is essentially defined via expression-to-action which uses list-to-action and atom-to-action.
;            If it is a user defined lambda, it goes to list-toaction and then *lambda makes a closure (formal parameters, body, and environment)
; IH: Assume that any expressioin within the lambda body or closure environment will return the correct result as R5RS Scheme.
; IS: So in the interpreter, when the lambda is evaluated, it makes a closure. And this in the closure, the arguments are evaluated, then the
;     arguments are bounded to them, and then the body is evaluated in the environment. This is shown in lines 129-132.
;; ===================================================================================================================


;; ===================================================================================================================
;Now let's focus on number 3, errors. In TLS, a lot of the functions have an extra parameter that ends in -f. These are usually build-f, table-f, or
;something of that nature. These basically do the same thing as Scheme and returns an error message but they are used in certain cases. For example
;entry-f is used when we try to find a variable not found in the environment. And in our interpreter, we generate these error messages.
;(define (entry-f name)
;   (begin
;     (display "Error:")
;     (display name)
;     (display "not in values.")
;      (newline)#f))

;(value '((lambda (x y) x) 1))  ;returns error
;(value '(car 5))               ;returns error
;(value '(5 3))                 ;returns error
;Although these messages may not be identical to R5RS errors, the conditions under which errors occur match. It's basically like entry-f is the Scheme error
;for undefined variable. build-f is the error for invalid. And ultimately, it does meet our standard of correctness.

; Base Case: : TLS defines error-handling by making functions like entry-f, build-f, and table-f to give errors like R5RS Scheme: undefined, invalid.
; IH: Assume that for any expression that results in an error in TLS it will return a similar error in R5RS.
; IS: While the exact error messages can be different from R5RS, they essentially say the same thing. And it is shown in lines 154-158.
;; ===================================================================================================================





#|
So let's start off with the base step of the interpreter.
We can say constants and symbols are the base case since they are not built from smaller TLS expression.
While lambda, cond, and functions are built of s-expressions. 
;; ===================================================================================================================
;; Base Cases
;; ===================================================================================================================

Base case 1: e is a constant (number, boolean),
;(meaning e table) → (*const e table) → returns e unchanged
;Semantics: [e]table = e (the value itself)


Base case 2: e is a variable (symbol)
;(meaning e table) → (*identifier e table) → (lookup-in-table e table initial-table)
;Semantics: [e]table = value bound to e in the table



;; ===================================================================================================================
;; Inductive Hypothesis
;; ===================================================================================================================
;For all S-expressions e' that are proper subcomponents of e,
;The evaluation function (meaning e table) works correctly on the other components
;In which it correctly returns the proper semantic value [e]table


;; ===================================================================================================================
;; Inductive Cases
;; ===================================================================================================================
Case 3: 'e' = (quote e)
;Subcomponent: e (not evaluated yet, but must be syntactically valid)
;By IH: The interpreter correctly recognizes e as valid syntax
;*quote e table) → (text-of e) = e (returns the value)
; Since the value holds true during the IS, the interpreter correctly recognizes e
; Meaning our interperter is working correctly.

Case 4:(lambda (params) body)
;params (must be s-list) and body (S-exp)
;The interpreter constructs closure (non-primitive (table params body))
;By IH: body is a simpler S-expression that evaluates correctly


Case 5: (cond (qi ai) ... (else an))
;Each qi and ai are simpler S-exps
;The Interpreter then calls the function (*cond sexp table) → (evcon clauses table)
;this means if cond is recognized as the valid syntax it calls for evcon which checks the clauses.
;Returns first ai where qi evaluates to #t
|#



;; ===================================================================================================================
;  Test Cases Demonstrating Correctness
;; ===================================================================================================================
#|
(value '5) ; => 5
(value '(quote hello)) ; => hello
(value '(lambda (x) x)) ; => (non-primitive ...)
(value '(cond ((#f 'wrong) (else 'right)))) ; => right
(value '((lambda (x) (add1 x)) 3)) ; => 4
(value '(((lambda (x) (lambda (y) (cons x y))) 1) 2)) ; => (1 . 2)
|#




#|
Now let's look at conditionals. As we know in TLS, conditionals are handled through the cond special form.
In addition to the else? predicate. Looking at our interpreter it handles these by recognizing cond expressions through 
the list-to-action function. It then process the clauses correctly through evcon.

(define (*cond e table)
  (evcon (cond-lines-of e) table))

(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) 
     (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))


(value '(cond (else 5)))                 ;returns 5
(value '(cond (#f 1) (#t 2) (else 3)))  ;returns 2
(value '(cond (#f 1) (#f 2) (else 3)))  ;returns 3
(value '(cond (#f 1)))                  ;returns error
; As we can see each results matches what we'd expect in TLS and R5RS. When there is no conditions just an else statement
; in both tls and R5RS the else value will be returned. When one condtion is true then it will return the the value associated with the condition
: when both condition are false then we will return the else value. All of this holds true for TLS and R5RS. This shows that it does meet our standard of correctness.



Now lets move onto the proofs
;; ===================================================================================================================
;; Base Cases
;; ===================================================================================================================

;Base case 1: (cond (else e))
;(meaning '(cond (else e)) table) → 
;(*cond '(cond (else e)) table) → 
;(evcon '((else e)) table) → 
;(meaning e table)
;Semantics: [cond (else e)]table = [e]table

;Base case 2: (cond)
;(meaning '(cond) table) → 
;(*cond '(cond) table) → 
;(evcon '() table) → 
;error (no else clause)
;Matches TLS behavior

;; ===================================================================================================================
;; Inductive Cases
;; ===================================================================================================================
;Case 1:
(cond (q1 a1) ... (else an)). 
;1. Evaluate q1 via (meaning q1 table)
;2. If #t: return (meaning a1 table)
;3. If #f: recur on remaining clauses
;4. Final else acts as base case

;By construction, this implements proper cond semantics:
;- Evaluates conditions in order
;- Returns first true branch
;- Handles else as catch-all





|#
;Now let's focus on number 5, atoms. In TLS and Scheme, atomic expressions like
;numbers, booleans, and primitive symbols evaluate to themselves. Our interpreter
;handles these through the atom-to-action dispatcher and *const action.

(define (atom-to-action e)
  (cond
    ((const-atom? e) *const)
    (else *identifier)))

(define (*const e table)
  (cond
    ((number? e) e)
    ((eq? e #t) #t)
    ((eq? e #f) #f)
    (else
     (build 'primitive e))))

;The test cases that go along with this
;(value '5)        ;returns 5
;(value '#t)       ;returns #t
;(value 'cons)     ;returns (primitive cons)
;(value '(atom? 5)) ;returns #t

;As we can see the result matches both TLS and R5RS behavior correctly.



#|
Moving onto the proofs for atom
;; ===================================================================================================================
;; Base Cases
;; ===================================================================================================================
;Base case 1: n is an integer
;(meaning n table) → (*const n table) → n
;Semantics: [n]table = n
; Since n is an integer it will evaluate to itself.

;Base case 2: we input a boolean
;(meaning #t table) → (*const #t table) → #t
;(meaning #f table) → (*const #f table) → #f
; Boolean primitives #t and #f will evaluate to themselves

;Base case 3: Primitive symbols (cons, car, cdr, etc.)
;(meaning 'cons table) → (*const 'cons table) → 
;(primitive cons)
;Semantics: [prim]table = tagged primitive

More test cases:
;1. Numbers: (atom? 5) → #t
;2. Symbols: (atom? 'x) → #t
;3. Pairs: (atom? '(1 2)) → #f
;4. Empty: (atom? '()) → #f
|#
