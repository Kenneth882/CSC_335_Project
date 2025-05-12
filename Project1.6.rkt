;; ===========================================================================================================
;; THIS IS SECTION 1.6 OF THE CS335 PROJECT
;; ===========================================================================================================
;; 1.6 Carefully explain the dependence of TLS on the underlying R5RS of DrRacket.  Focus, in particular,
;; on the mechanics of function calling: which system does which work?
;; ===========================================================================================================
;; 1.6 Explain Interaction with R5RS
;; - How does TLS depend on R5RS
;; - Analyze what TLS relies on from the underlying R5RS interpreter (e.g., DrRacket).
;; - Focus especially on:
;;     - Primitive operations (like +, car, cons)
;;     - Function application mechanics
;;     - How much evaluation is performed by TLS vs. by Scheme itself
;; ===========================================================================================================



#|
So let's start with focusing on DrRacket for a bit. This is what we use to implement Scheme, EOPL, and other
different languages. The TLS Interpreter is written in Scheme. And in "The Little Schemer" it says that:

"It is our belief that writing programs recursively in Scheme is essentially simple pattern recognition. Since
our only concern is recursive programming, our treatment is limited to the whys and wherefores of just a few
Scheme features: car, cdr, cons, eq?, null?, zero?, add!, sub!, number?, and, or, quote, lambda, define, and
cond. Indeed, our language is an idealized Scheme."

TLS handles the high-level work because it does a lot; it parses the expression, meaning it takes the raw input and
then breaks it down into structural parts. Looking for parameters, functions, and arguments. It then decides what kind of
operator it is, by expression-to-action. It can also use list-to-action, atom-to-action. But more commonly it uses expression.
It creates environments and extends them. And it knows when to call primitives or apply user functions. Meanwhile R5RS, the TLS
interpreter relies on it for low-level execution, like executing the operations and run the Scheme code itself.
TLS fully controls the high level things such as breaking down expressions, creating and applying closures, building and extending
environments, and determining when and where a primitive needs to be applied. However, whenever a primitive operation is met,
TLS calls into the Scheme system to perform the actual low level computation.


Focusing on the operations above, let's primarily focus on car, cdr, and cons as a working example. What TLS does is that
it sees these primitives, recognizes them, and wraps them. That is why we have (primitive car), (primitive cdr), as the return. This
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


R5RS steps in only when primitives like car, cdr, cons, etc. That’s when the host language takes over. Meanwhile TLS is doing
everything else, focusing on apply-closure and enviornment tracking. A real world example would be like a person taking an exam.
We use our hands to write down our code (R5RS), meanwhile our brain (TLS) does all the heavy lifting—deciding what to do, in what
order, and how to apply rules. TLS evaluates structure, builds closures, and interprets meaning. R5RS just follows those instructions
and handles the low-level operations like +, car, cons, etc.
|#




#|
Now in the focus of function calling and the mechanics for that. The TLS interpreter builds closures from lambda expressions but R5RS does this
regularly when evaluating lambdas. The interpreter is responsible for breaking down expressions and it does it in a smart way. So if we have a lambda function
in the interpreter, it builds a closure. A closure is a data structure and it has parameters, body, and an environment.
(define (tls-apply-closure closure vals)
  (let*
      ((saved (first closure))
       (formals (second closure))
       (body (third  closure))
       (new-env (extend-table formals vals saved)))
    (meaning body new-env)))

Now this is the apply-closure function function in TLS, we called it tls-apply-function. So what this does is that it extracts the closure elements,
the saved environment, the formal parameters, and the body. And then it makes a new environment by extending the environment and helps bound everything
correctly here. After that, an important line is (meaning body new-env). This is where TLS actually evaluates the function body in the updated environment.
On a more broad and general breakdown, lets say that the function is a user defined lambda, then the interpreter uses its own rules and environment. If the
function is just a primitive, then the interpreter calls the R5RS primitive. If it is neither, we will likely get an error message.



Now for a few examples of this, I'll cover examples with regular operators like +, *. And then TLS built in car, cdr, cons.
And then TLS not built it, like append, reverse.
1) (value '((lambda (x) (+ x 1)) 2)) 
; The first step would be that TLS creates a closure, so (non-primitive current-env (x (+ x 1)))
; The second step is to extend the environment with x=2
; The third step is to evaluate `(+ x 1)` in the new environment
; The fourth step is to compute the actual `+` operation.
; Final answer is 3.


2) (value '((lambda (x) (cons x '(1 2 3))) 'a))
; The first step is to create a closure, so (non-primitive () (x) ((cons x '(1 2 3))))
; The second step is to extend the environment, so x= 'a
; The third step is to evaulate and use the cons;
; Final answer is (a 1 2 3)


3) (value '((lambda (x) (append x '(1 2 3))) '(a b)))
; ERROR. We will get an error message here because even though R5RS knows append and reverse, TLS Interpreter doesn’t automatically pass through everything.
; It only knows to call what it recognizes as a primitive. So unless TLS is extended to handle append or reverse, it doesn’t send the call to Scheme. 
; However, it is a primitive in Scheme. Like in regular R5RS, we can do (reverse '(1 2 3)) -> (3 2 1)
|#
