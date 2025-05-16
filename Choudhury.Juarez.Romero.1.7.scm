


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
; this process would keep repeating until we reach a stopping condition, so thats the basics of a loop in lambda calculus!
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
;so given the defenition  Y==(λx.f(xx))(λx.f(xx))F
;once we subsititue we get (λx. F (x x)) (λx. F (x x))
;then this implies F ((λx. F (x x)) (λx. F (x x)))
; so after plugging in we got back to where we started so it shows that Y F= F( Y F)



;How does Y-Combinator actually imply reccursion informaly:
;This section will be used to clarify our findings and deviate from mathematical terms to english since depending on who is reading our
;project, a beginner or an expert  programmer we should hope that our findings can be comprehendable to everyone.
;Regular reccursion is usually used in the context of a function/program calling back on the same function until it hits a potential base case
;Such as in factorial when the  function  hits 0 it returns the value 1 to the previous call and that call multiplies that value with its current value
; until it reaches all the way to the top value, which is like working backwords. However The Y-Combinator does an intresting metheod where
; it doesent call on its parent function instead it constructs a function which recives itself as an argument.
;So insted of calling the function itself over and over again the Y-combinator passes itself as a function without
;refering to itself by name.This therfore mimics traditional reccursion because the function passing itself will always take in the result of the previous call since
; its calling itself so the work done by the previous call will simply be passed down to itself until it reaches a base case and then will work itself back up like regualr reccursion!





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
;In our case ( f(x x)) is evaluated instantly  meaning that we call the parameter into the function, but it keeps calling itself an infinite amount of times
;due to it being a value and fufilling the closure properties. So we keep calling ( f(xx)) (f(x x)) an infinite amount of times without f actually being executed
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
          (* n (self (- n 1))))))) ;Fufills y combinator by not calling the function itself and instead implying reccursion

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

(define sumation( Y sum-maker)) 

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
