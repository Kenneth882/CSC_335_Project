;; 1.6 Carefully explain the dependence of TLS on the underlying R5RS of DrRacket.  Focus, in particular,
;; on the mechanics of function calling: which system does which work?

;; ============================================================================
;; 1.6 Explain Interaction with R5RS
;; - How does TLS depend on R5RS
;; - Analyze what TLS relies on from the underlying R5RS interpreter (e.g., DrRacket).
;; - Focus especially on:
;;     - Primitive operations (like +, car, cons)
;;     - Function application mechanics
;;     - How much evaluation is performed by TLS vs. by Scheme itself
;;
;; ============================================================================


#|
So let's start with focusing on DrRacket for a bit. This is what we use to implement Scheme, EOPL, and other
different languages. The TLS Interpreter is written in Scheme. And in "The Little Schemer" it says that
" It is our belief that writing programs recursively in Scheme is essentially simple pattern recognition. Since
our only concern is recursive programming, our treatment is limited to the whys and wherefores of just a few
Scheme features: car, cdr, cons, eq?, null?, zero?, add!, sub!, number?, and, or, quote, lambda, define, and
cond. Indeed, our language is an idealized Scheme."


Focusing on the operations above, let's primarily focus on car, cdr, and cons as a working example. What TLS does is that
it sees these primitives, recognizes them, and wraps them. That is why we have (primitive car), (primitive cdr), etc. This
is why there exists primitive, non-primitive, and apply-primitive. 
;((expression-to-action 'car) 'car '())       ;returns (primitive car)
;((expression-to-action 'cdr) 'cdr '())       ;returns (primitive cdr)
;((expression-to-action 'cons) 'cons '())     ;returns (primitive cons)

What R5RS does here it that it actualy implements the primitives car, cdr, cons, etc. The way I think of it is a big helping
hand relationship.
(value '(car '(a b c d e f))). If we were to run this example using the TLS interpreter, it would recognize that car is a primitive
and then R5RS would do the actual work and return 'a' (not actually return in quotes but just a).
(value '(car '(a b c d e f)))        ;returns a
(value '(cdr '(a b c d e f)))        ;returns (b c d e f)
(value '(cons '(1 2 3) '(a b c)))    ;returns ((1 2 3) a b c)
|#



#|
Now in the focus of function calling and the mechanics for that. The TLS interpreter focuses a lot on closures while R5RS focuses on
lambdas usually. The interpreter is responsible for breaking down expressions and it does it in a smart way. So if we have a lambda function
in the interpreter, it builds a closure. A closure is a data structure and it has parameters, body, and an environment. 
|#