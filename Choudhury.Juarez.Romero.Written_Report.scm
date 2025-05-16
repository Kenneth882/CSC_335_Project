; CSC 33500
; Professor Troeger
; Project Project Spring 2025 Part 1
; TLS Interpreter + Y-Comb + Research (1.1 - 1.7)


; Group Members for Project: 
; Alexis Juarez Gomez
; Hamim Choudhury
; Kenneth Romero Linares


;;=================================================================================================================================
;;Section 1.1: Implement TLS in pure functional R5RS, providing a full development for the code including specifications for each
;;function.  Give examples of TLS programs which work with your interpreter.
;;=================================================================================================================================
;;
;;
#|

Now this is what we were told to do according to the project doc given by the Professor. Our thought process for this was simple:
read chapter 10 of “The Little Schemer” and then copy the code from there into DrRacket R5RS Scheme. When we were first introduced
to this project, we had already read “The Little Schemer”, but not up to chapter 10. So this was definitely new to us. However, chapter
10 did build off of everything from the previous chapters so it was a lot easier. 


Kenneth started the project first, he made the Github repository and began Section 1.1 by extracting the code and putting it all in Racket.
At first, this was very basic, it just included all the helper functions, the aliases, and the functions DIRECTLY from the book. But this was
not enough. Hamim and Alexis then began to work on making it run properly and return the correct result for certain test cases. At this point,
we have all decided that Kenneth was going to move on to section 1.2 and Hamim and Alexis were going to finish 1.1, where Hamim was responsible
for making the file organized, fixing the functions, making test cases, etc. Alexis was mainly responsible for the proofs and the specifications
of the functions. This did take a while as there were a lot of functions and certain functions had to be ordered in a specific way or there would
be “Undefined Identifier” errors. Professor Troeger also gave us test cases to use with our interpreter. Once these test cases were added our
interpreter did return the correct result. After meeting 1, Professor Troeger told us to work on having more complex test cases and for more
functions. This was completed, almost every function has test cases. They are commented out and the only tests that are not commented are the ones
given by the professor.


In order to complete this, we had to break our interpreter into different sections. The first section consisted of helper functions and alias's.
We had first, second, third, question-of, text-of, etc etc. The second section would consist of table, build, and entry functions. The third function
would then consist of the type predicates. This is where we had primitive?, non-primitive?, atom?, :atom?. The fourth section would then consist of the
action implementations such as *const, *cond, *lambda, *application, evcon, evlis, etc. The fifth section would consist of the expression and dispatchers,
expression-to-action, list-to-action, and atom-to-action. The sixth and last section would then have the error functions. 

|#
;;
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.2: Give an inductive definition of the fragment of Scheme implemented by TLS.  Using this definition, write a purely functional
;R5RS syntax checker for TLS.  While your syntax checker should not evaluate its input, it should be as complete as you can make it.
;It should, at a minimum, (i) detect basic errors such as malformed cond and lambda expressions; (ii) detect when primitives are applied to
;the wrong number of arguments; and (iii) detect the presence of unbound variables.
;;=================================================================================================================================
;;
;;
#|


|#
;;
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.3: After giving a specification for the environment subsystem of TLS, prove that your implementation satisfies this specification.
;Then change the representation of environments to use lists of bindings rather than the names-values pairs shown in the text, and show that
;the altered representation both satisfies your specification and works with the rest of the interpreter.
;;=================================================================================================================================
;;
;;
#|

We did this by creating the functions extend-env,extend-env* and apply-env which were used as a way to create a binding system. In order to verify
that it was compatible with the interpreter we used our original 1.1 TLS interpreter and then we changed the original environment to the new one giving
us a fully working interpreter with a binding system

|#
;;
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.4: Research closures and lexical scope, and prove that (your implementation of) TLS implements these correctly. Your writeup will
;need to include enough information on closures and lexical scope to allow a meaningful correctness discussion.  Your argument will use
;structural, as well as other inductions. 
;;=================================================================================================================================
;;
;;
#|

Because this was a fairly complex section of the project, it did require a lot of research from a variety of different resources. Kenneth did most of the
work for this section and to better organize it, he added his notes on a Google Doc which is linked below. This doc will also be submitted for interview 2
and for the final project as well. 
https://docs.google.com/document/d/1CKyYgchK5oChhL6ZRU6buQEhEG78gxKq_Pgxfek-oX8/edit?usp=sharing

In 1.4 we were asked to talk about lexical scoping and closures. At first we did research on Dynamic Vs lexical scoping to figure out the differences between
the two. After our findings we proved that our Current Tls interpreter was lexically scoped and we used a structural induction to prove that.

|#
;;
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.5: After carefully identifying a standard of correctness, prove that your implementation of TLS is correct according to that
;standard.
;;=================================================================================================================================
;;
;;
#|

For this section, the confusing part for us was actually understanding what the problem was asking. We didn't know what "standard of correctness"
really meant. The issue was when we Googled it, "what is standard of correctness", it brought out information regarding the law and court procedures.
This did help us a little because one word was common, "reasonableness". And working from there, we decided that this meant, given our interpreter
how is it reasonably correct (meaning it returns the right answer). Specifically,  what it means for our interpreter to work correctly. This includes
what it should do for a given input and proving that it behaves as expected.

Once we had the standard of correctness understood and defined, the next step was proving it. And proving it would be fairly simple. The reason why is because
in TLS, we can break it down into different sections and then prove it from there. The way we broke it down was first beginning with primitives and functions. We
were honestly going to stop there, but thought that it would not be enough because 1) TLS had error messages like build-f, entry-f, table-f and those were error
messages. And then conditionals and atoms were added by Alexis.

Our full standard of correctness and its proof can be found in the 1.5 file, but here it is as well:
;; ===================================================================================================================
;;STANDARD OF CORRECTNESS FOR OUR TLS INTERPRETER:
#|
Our TLS interpreter is correct if, for every valid TLS expression, it produces the same result as R5RS Scheme, where the expression is within the subset of
Scheme supported by The Little Schemer (TLS). That means our interpreter should evaluate expressions in the same way as an R5RS interpreter, assuming
functional behavior and TLS-specific constraints. Basically semantic preservation. Further, our interpreter should also consider and do lexical scoping,
make closures properly, and evaluate expressions as well.

1) Primitive Evaluation. The primitive procedures like car, cdr, cons, atom?, etc must produce the same results as their R5RS Scheme equivalents.

2) Functions and Closures. In TLS, function definitions are represented as closures (formal parameters, a function body, and the environment). Our interpreter must ensure
that closures maintain proper bindings for parameters during the function application, and evaluates the body using lexical scoping rules thus resulting in the
correct result, no errors or anything incorrect.

3) Error Handling. The interpreter must detect invalid expressions, such as unbound variables or incorrect function applications. In TLS, they have error functions such as
entry-f, table-f, and build-f. Our implementation must ensure that such errors are correctly identified and outputted like R5RS Scheme. 

4) Conditionals.  In TLS and Scheme, conditionals such as cond, if, and else must correctly evaluate branches based on the first true condition. Our interpreter must ensure
that conditions are checked in order, and the result expression for the first true test is returned. This should be consistent with R5RS Scheme.
|#


We then proceded to prove this via structural induction. We then walked through each case above and gave through test cases and proofs as well.
For primitive evaluations, we kept a close eye on atoms as they would just return themselves. Same as booleans. For functions and closure, it was a bit more
complex as we focused on how functions are represented as lambda expressions.

A closure has
formal parameters, the body, and the environment. *application evaluates the function and its arguments, and then applies the function
using tls-apply. Basically lambda expressions => identified via expression-to-action => dispatched through list-to-action => to *lambda => makes the closure.
The functions body must be evaluated in a new environment where the formal parameters are bound to the values. We need extend-table because
that is how the new environment is created, the new one goes in front of the previous one. And lookup-in-table is needed since variables are looked up in the
table. And then this finds the correct value.



For conditionals
Conditionals are evaluated using cond special form. Each clause in a cond
expression is a pair: a test expression and a result expression. The clauses are checked in order until the first one that evaluates to true
is found and then its result is returned. Our interpreter uses *cond, which calls to the helper function evcon. The function evcon` walks through the
clauses, checking each one with meaning and returns the value of the corresponding result expression. If no conditions match, we have the else.

#|
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
|#

;(value '(cond ((#f 'hello) (#t 'world))))                ;world
;(value '(cond ((zero? 1) 'no) ((zero? 0) 'yes)))         ;yes
;(value '(cond ((number? 'x) 'lebron) (else 'hamim)))     ;hamim
;(value '(cond (else 'noclausehere)))                     ;noclausehere
;(value '(cond ((#f 'x) (#f 'y) (else 'z)))               ;z
;(value '(cond ((#f 'a))))                                ;we get an error here because there is no else clause.



;Base Cases: 1)When a cond expression only contains a single else clause the interpreter directly evaluates the expression `e` and returns that value.
;            2)If there are no clauses, then we get an error message because a) nothing to evaluate and go through and b) no else case either.

;IH: Assume that all expressions used in cond q1, q2,.. and the results a1, a2,.. are evaluated correctly by the interpreter.

;; IS
;; For a skeleton cond
#|
(cond
  (q1 a1)
  (q2 a2)
  ...
  (else an)
 )
|#

;The way this works is that it goes through each condition one by one IN ORDER. So q1 first, then q2, then q3 and so on and so forth. So if q1 is true, it returns
;a1. However, if it is false, then it goes to q2 and does the same thing (check is condition q2 is true or not) if not true, go to q3. But if true, return a2.
;And the big picture is if neither q1, q2, etc etc are not true. We go to an else clause. And whatever the else clause is, we need to return it. So we need clauses
;and we need an else clause if we are using cond. ;Because conditions are checked in order and only the first truthy is evaluated, this follows Scheme semantics and
;ensures correct behavior. This proves that conditionals in our TLS interpreter are correct.

|#
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.6: Carefully explain the dependence of TLS on the underlying R5RS of DrRacket.  Focus, in particular, on the mechanics of function
;calling: which system does which work?
;;=================================================================================================================================
;;
;;
#|

I think out all the sections, besides section 1.1, this was a fairly straightforward section. We knew that TLS is basically a subset of Scheme,
Professor Troeger mentioned it in class and the book says it itself. " It is our belief that writing programs recursively in Scheme is essentially
simple pattern recognition. Since our only concern is recursive programming, our treatment is limited to the whys and wherefores of just a few Scheme
features: car, cdr, cons, eq?, null?, zero?, add!, sub!, number?, and, or, quote, lambda, define, and cond. Indeed, our language is an idealized Scheme."


The way to approach this was to understand the difference and compare the TLS Interpreter vs the actual DrRacket R5RS Scheme. And then we have to
understand what the function mechanics is. And when it speaks about functions, it clearly means lambdas and then closures. This was brought up in class
and in office hours a lot. A closure is basically formal parameters, body, and environment. I was focusing primarily on user defined lambda functions as
that is what I believe the question was asking. The interpreter is built on top of the Scheme environment, that is clear to us. And then focusing on primitives,
which plays a main part, primitive ops like car, cdr, cons TLS goes to R5RS for help. If the op is a user defined function, TLS makes the environment and then
evaluates there. But if its primitive, then it calls its big brother R5RS. TLS performs the interpretation and environment handling at the high level, while relying
on DrRacket’s primitive operation execution. TLS itself is a Scheme program, it is a subset of Scheme. When TLS applies a primitive function, it it then send to
DrRackets R5RS built in primitives.


We divied this up into sections, what TLS does and what R5RS does.
Based on our interpreter, what TLS is responsible for is
- Making closures for lambda expressions via tls-apply-closure
- How environments and closures are managed via extend-table and lookup-in-table
- Function applications
- Expression Dispatching (expression-to-action is a good example)
- Parsing expressions also using expression-to-action
- Recognizing lambdas and applying them.


Meanwhile, R5RS is responsible for
#|
- Executing built-in operations: car, cdr, cons, null?, eq?, etc etc
- Evaluating Scheme-level primitives inside tls-apply-primitive
- Performing the computations
- Supporting predicate checks because in our interpreter we often use number? and this is a prime example
|#

|#
;;
;;
;;=================================================================================================================================





;;=================================================================================================================================
;Section 1.7: Drawing on Chapter 9 of The Little Schemer, equip your TLS with recursion to form TLS-REC, using the Y-combinator. Research
;Y-combinators, and prove that the implementation you use actually implements a Y-combinator. Explain, in detail, how the Y-combinator implements
;recursion.  Include interesting examples of recursive programs written TLS-REC. 
;;=================================================================================================================================
;;
;;
#|

IN 1.7, Y combinator, after researching lambda calculus we dived into figuring out how Y combinator would work in Scheme. Doing this we found out various
examples like factorial and length which could be found using the Y-combinator.

|#
;;
;;
;;=================================================================================================================================
