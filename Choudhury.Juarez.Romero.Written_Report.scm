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
