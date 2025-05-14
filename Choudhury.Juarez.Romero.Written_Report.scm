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
;;;
Our TLS interpreter is correct if, for every valid TLS expression, it produces the same result as R5RS Scheme where the expression is within the subset of
Scheme supported by The Little Schemer (TLS). That means our interpreter should evaluate expressions in the same way as an R5RS interpreter, assuming pure
functional behavior and TLS-specific constraints.

1) Primitives. We wish to focus on the primtive operations. In TLS, there are primitives such as +, car, cdr, cons, null?, eq?, zero?, atom?, etc, etc
and we want these to return the same result as R5RS Scheme.

2) Functions. For lambda functions, TLS represents them as closures (formal parameters, body, environment) and we want to make sure that there
is proper binding for the parameters. We want to ensure lexical scoping. And ultimately the correct evaluation of the body.

3) Errors. In TLS, we are introduced to things such as build-f, entry-f, etc, etc. These are just error messages that are commonly for undefined,
incorrect number of arguments, primitive errors. And TLS widely says the error.

4) Conditionals. In TLS and Scheme, we have cond, if, and else? These should go into the correct branch and return the result associated with that branch. We
can have long conditional statements but regardless it should return the right answer. It's sort of like our names and values. Names is the branch and then we
return the value associated with the name.

5) Atoms. We have an atom? in TLS and we can make it in R5RS Scheme. If we have an atomic expression, it should always return themselves. Meaning numbers and
booleans should return themselves.
;;;

|#
;;
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
evaluates there. But if its primitive, then it calls its big brother R5RS. 

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


|#
;;
;;
;;=================================================================================================================================
