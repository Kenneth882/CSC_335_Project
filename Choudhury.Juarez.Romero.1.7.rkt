;1.7 Y-combinator TLS-REC
;------------------------------------------------------------------------------------------------
;For TLS-REC we will use our inital interpetrer as well as the changes we did with 1.3 to show the power of the
;Y-Combinator


( define empty-env '())


(define (extend-env name val env) 
  (cons (list name val) env))


(define (extend-env* names vals env)
  (if (null? names)
      env
      (extend-env* (cdr names)
                   (cdr vals)
                   (extend-env (car names) (car vals) env))))

(define(apply-env env name)
  (cond ((null? env)
         (error 'apply env(format "unbound identifier: ~a" name))) 
        ((eq? name (car(car env)))
         (cadr(car env)))
        (else
         (apply-env(cdr env) name))))


(define (extend-table formals vals table)
  (extend-env* formals vals table))


(define 13-env
  (extend-env* '(x y)
               '(1 2)
               (extend-env* '(z)
                            '(3)
                            empty-env)))

(apply-env 13-env 'x) 
(apply-env 13-env 'y) 
(apply-env 13-env 'z)


(define env1
  (extend-env* '(a b c) '(1 2 3) empty-env))

(apply-env env1 'a) 
(apply-env env1 'b)
(apply-env env1 'c) 


(define env3
  (extend-env* '(x y) '(42 43)
    (extend-env* '(p q) '(5 6)
      (extend-env 'r 100 empty-env))))

(apply-env env3 'x) 
(apply-env env3 'p) 
(apply-env env3 'r) 


(define (atom? x)
  (and (not (pair? x)) (not (null? x))))


(define (count-elements lst)
  (if (null? lst)
      0
      (+ 1 (count-elements (cdr lst)))))



(define (add1 n)
  (+ n 1))



(define (sub1 n)
  (- n 1))


(define first car)



(define second cadr)



(define third caddr)




(define (else? x)
  (and (atom? x) (eq? x 'else)))



(define question-of first)



(define answer-of second)




(define cond-lines-of cdr)



(define function-of car)



(define arguments-of cdr)




(define text-of second)



(define table-of first)



(define formals-of second)



(define body-of third)


(define (const-atom? a)
  (or (number? a)
      (eq? a #t) (eq? a #f)
      (memq a '(cons car cdr null? eq? atom? zero? add1 sub1 number?
                     + - * / < > <= >=))))



(define (extend-table formals vals table)
  (extend-env* formals vals table))


(define (meaning e table)
  ((expression-to-action e) e table))


(define (initial-table name)
  (error "Unbound identifier" name))




(define (check-set list1)
  (cond
    ((null? list1) #t)
    ((member (car list1) (cdr list1)) #f)
    (else
     (check-set (cdr list1)))))


(define (check-equal-len-list list1 list2) 
  (cond
    ((and (null? list1) (null? list2)) #t)
    ((or (null? list1) (null? list2)) #f)
    (else
     (check-equal-len-list (cdr list1) (cdr list2)))))



(define build list)
(define new-entry build)


(define (primitive? fun)
  (and (pair? fun) (eq? (first fun) 'primitive)))


(define (non-primitive? fun)
  (and (pair? fun) (eq? (first fun) 'non-primitive)))



(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))



(define (*quote e table)
  (text-of e))



(define (*identifier e table)
  (apply-env table e) )     



(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e)))) 



(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))




(define (*cond e table)
  (evcon (cond-lines-of e) table))



(define (evlis args table)
  (if (null? args)
      '()
      (cons (meaning (car args) table) (evlis (cdr args) table))))

(define (tls-apply fun vals)
  (cond
    ((primitive? fun) (tls-apply-primitive (second fun) vals))
    ((non-primitive? fun) (tls-apply-closure (second fun) vals))
    (else
     (error "tls-apply: not a function" fun))))


(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))    


(define (tls-apply-primitive name vals)
  (cond
    ((eq? name '+) (apply + vals))
    ((eq? name '-) (apply - vals))           
    ((eq? name '*) (apply * vals))          
    ((eq? name '/) (apply / vals))           
    ((eq? name '<) (apply < vals))           
    ((eq? name '>) (apply > vals))           
    ((eq? name '<=) (apply <= vals))         
    ((eq? name '>=) (apply >= vals))        
    ((eq? name 'cons)  (cons  (first vals) (second vals)))
    ((eq? name 'car)   (car   (first vals)))
    ((eq? name 'cdr)   (cdr   (first vals)))
    ((eq? name 'null?) (null? (first vals)))
    ((eq? name 'eq?)   (eq?   (first vals) (second vals)))
    ((eq? name 'atom?) (atom? (first vals)))
    ((eq? name 'zero?) (zero? (first vals)))
    ((eq? name 'add1)  (+ (first vals) 1))
    ((eq? name 'sub1)  (- (first vals) 1))
    ((eq? name 'number?) (number? (first vals)))
    (else (error "unknown primitive" name))))


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
  



(define (atom-to-action e)
  (cond
    ((const-atom? e) *const)
    (else *identifier)))





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

(define (set-f)
  (begin
    (display "Error: Not a set, duplicate elements found.")
    (newline)
    #f))



(define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))



(define(table-f name)
   (begin
      (display "Error:")
      (display name)
      (display "Not found in the table")
      (newline)#f))



(define(eq-list-f)
   (begin
        (display "Error: Lists are not of equal length.")
        (newline)
        #f))


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
;so given the defenition  Y=≈(λx.f(xx))(λx.f(xx))F
;once we subsititue we get (λx. F (x x)) (λx. F (x x))
;then this implies F ((λx. F (x x)) (λx. F (x x)))
; so after plugging in we got back to where we started so it shows that Y F= F( Y F)



;How does Y-Combinator actually imply reccursion informaly:
;This section will be used to clarify our findings and deviate from mathematical terms to english since depending on who is reading our
;project, a beginner or an expert  programmer we should hope that our findings can be comprehendable to everyone.
;Regular reccursion is usually used in the context of a function/program calling back on the same function until it hits a potential base case
;Such as in factorial when the  function  hits 0 it returns the value 1 to the previous call and that call multiplys that value with its current value
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
;In our case ( f(x x)) is evaluated imediatlly meaning that we call the parameter into the function, but it keeps calling itself an infinite amount of times
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

;need to load up 1.3 and 1.1


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



 (value
 '((Y (lambda (sum)
        (lambda (n)
          (cond ((zero? n) 0)
                (else (+ n (sum (sub1 n))))))))
   4))

;->> returns 10

(value
 '((Y (lambda (fact)
        (lambda (n)
          (cond
            ((zero? n) 1)
            (else (* n (fact (sub1 n))))))))
   4))
;; Expected output: 24

(value
 '((Y (lambda (len)
        (lambda (xs)
          (cond
            ((null? xs) 0)
            (else (add1 (len (cdr xs))))))))
   (quote (a b c d))))
;; Expected output: 4














;-------------------------------------------------------------------------------------------------