; This is for section 1.5 of the project

;; ==================================================================================================
;1.5 After carefully identifying a standard of correctness, prove that your implementation of TLS is
;correct according to that standard.
;; ==================================================================================================




;; ===================================================================================================================
#|
So the hardest part for this section for us was to essentially understand what it means when the problem says "standard of
correctness". And how to actually prove it.
Beginning with the standard of correctness, to us it means clearly defining what it means for our interpreter to work correctly.
This includes what it should do for a given input and proving that it behaves as expected.
|#
;; ===================================================================================================================




;; ===================================================================================================================
;;STANDARD OF CORRECTNESS FOR OUR TLS INTERPRETER:
#|
Our TLS interpreter is correct if, for every valid TLS expression, it produces the same result as R5RS Scheme where the expression is within the subset of
Scheme supported by The Little Schemer (TLS). That means our interpreter should evaluate expressions in the same way as an R5RS interpreter, assuming pure
functional behavior and TLS-specific constraints.

1) Primitives. We wish to focus on the primtive operations. In TLS, there are primitives such as +, car, cdr, cons, null?, eq?, zero?, atom?, etc, etc
and we want these to return the same result as R5RS Scheme.

2) Functions. For lambda functions, TLS represents them as closures (formal parameters, body, environment) and we want to make sure that there
is proper binding for the parameters. We want to ensure lexical scoping. And ultimately the correct evaluation of the body. It should respect the

3) Errors. In TLS, we are introduced to things such as build-f, entry-f, etc, etc. These are just error messages that are commonly for undefined,
incorrect number of arguments, primitive errors. And TLS widely says the error.

4) Conditionals. In TLS and Scheme, we have cond, if, and else? These should go into the correct branch and return the result associated with that branch. We
can have long conditional statements but regardless it should return the right answer. It's sort of like our names and values. Names is the branch and then we
return the value associated with the name.

5) Atoms. We have an atom? in TLS and we can make it in R5RS Scheme. If we have an atomic expression, it should always return themselves. Meaning numbers and
booleans should return themselves.
|#




;; TLS s-expressions can be:
;;   - Constants: numbers, booleans
;;   - Symbols: variables
;;   - Quoted expressions
;;   - Lambda expressions
;;   - Conditionals (cond), (if), (else)

(define (value e)
  (meaning e '()))

(define (meaning e table)
  ((expression-to-action e) e table))

(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))

;; expression-to-action determines which case to apply based on syntax.

#|
So let's start off with the base step of the interpreter.
We can say constants and symbols are the base case since they are not built from smaller TLS expression.
While lambda, cond, and functions are built of s-expressions. 


=============================================
Base Cases
=============================================

Base case 1: e is a constant (number, boolean),
;(meaning e table) → (*const e table) → returns e unchanged
;Semantics: [e]table = e (the value itself)


Base case 2: e is a variable (symbol)
;(meaning e table) → (*identifier e table) → (lookup-in-table e table initial-table)
;Semantics: [e]table = value bound to e in the table



===========================================
Inductive Hypothesis
===========================================
;For all S-expressions e' that are proper subcomponents of e,
;The evaluation function (meaning e table) works correctly on the other components
;In which it correctly returns the proper semantic value [e]table


==========================================
Inductive Cases
==========================================

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

=============================================
;  Test Cases Demonstrating Correctness
=============================================
#|
(value '5) ; => 5
(value '(quote hello)) ; => hello
(value '(lambda (x) x)) ; => (non-primitive ...)
(value '(cond ((#f 'wrong) (else 'right)))) ; => right
(value '((lambda (x) (add1 x)) 3)) ; => 4
(value '(((lambda (x) (lambda (y) (cons x y))) 1) 2)) ; => (1 . 2)

|#
