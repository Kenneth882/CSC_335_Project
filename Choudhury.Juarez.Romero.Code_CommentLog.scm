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


; 4/12-Kenneth(Comments Below)
; 1.1 is basicly a translation of TLS from TLS language into R5RS. I do notice that some functions from the book are repeated so i think the outline
; for the interpreter would be to get the simple functions and helpers out of the way first, that way we can keep refering to them and avoid redundent code.
; Initially i wll focus on just pure translation and then after everything is translated I will focus on connecting the important components

; 4/13/25 - Alexis (Comments Below)
; 1.1 of the project is based on TLS chapter 10. The implementations of the the function.
; One of the important things I have noticed are most functions are tail recursive (lookup-in-entry-helper, lookup,entry, etc.)
; This will be crucial for the proofs required from 1.5 so for now I have made a seperate file containing the proofs. 
; Before jumping into the proofs kenneth proposed we finish building the interperter so for now the proofs are not needed. 
; However, I labled each code with either T Recursion or Recursion so we will know in the future what proof will be needed
; for each function.


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

; 4/14-Kenneth(Commments Below)
; I implememnted most of TLS straight from the book, some of the functions still need to be linked.Most of the test cases that i did work with the function
; on its own, however there are certain functions that connect that have some logical errors to them, so we will hopfully work on fixing that. Since TLS
; had some repeated functions that did diffrent things we still have to clean and fix that so that each function can past every test case.

; 4/14-Alexis(Comments Below)
; I reviewed the code Kenneth implemented and fixed some errors, and added some of the basic functions from the book TLS. 
; Kenneth explained the outline and how some of the functions are repeated and some of the logic in TLS is flawed.


; 4/16/25 - Hamim (Comments Below)
; Today was just completing the build function in TLS, what this function does is that it returns an entry if it satisfies two conditions. The
; first condition being that the names list does not contain duplicates, aka is a set. And the second condition being that the values list and
; names list are of equal length. Both of the conditions have their own function, check-set and check-equal-len-list. Kenneth had already begun
; a basic outline of it, I just added onto it and finalized it. Alexis and myself were working on the pre and post conditions as well.


; 4/17/25 - Hamim (Comments Below)
; Action functions.

; 4/19-Kenneth (Comments Below)
; Started on the Syntax checker for TLS.Since we have a lot of functions for TLS I decided to have two refrences, conditons and special conditions
; Conditions will be all the operations that can be easily checked such as some of the built in operations and some primitives. Since some
; operations will be more complex like lambada where we will probably have to reccur to check all the other operations inside it we can always refer
; to the condtions to show if the arguments inside them follow the correct format.


; 4/28/25 - Alexis (Comments Below)
; Since most of the interpreter is done Hamim volunteered to clean up the code. We came accross an issue when using the test expressions 
; Professor Troeger provided. We concluded it was due to apply, instead of using the apply we implemented through TLS, the function *application
; was using the built in apply. After discovering that issue, Hamim uncovered other issues with our initial-table and new entry.
; After looking into apply I started working on syntax-checker. Kenneth already started the outline. I added the pre and post condition.
; I also implemented functions such as member?, duplicates, check-cond(not fully done), and error messages.


; 4/29/25 - Hamim (Comments Below)
; Adding on to Alexis's comments. Yes, there were errors when certain test cases were run. These errors were annoying because it let to the same few
; functions. And those functions were linked to other functions. It was like a loop of errors in a sense. There were two main issues. My build function,
; the apply function, and the primitive and non-primitive functions. The root errors were 1) something was not a procedure, mcar errors, and mcdr errors.
; In order to solve this, I spent all of today reading TLS carefully. I noticed that we did have some missing functions, spelling errors, and we made some
; functions a little more complex than it should have been. We were missing quote, lambda, and our action functions were wrong as well. The value and meaning
; were also incorrect.


; 4/29-Kenneth(Comments Below)
; After My inital layout of the syntax checker i realized that some of the Design was not correct. We dont really need a special-checker since
; each of the functions like lambda,cond,if ect does its own unique thing so refering to that would be redundant.I'm still not finished with it but most of the
; basic operations are done.The specific TLS functions still need to be checked and also need to work on showing specific
; error messages instead of just outputting false.

; 4/29-Alexis (Comments Below)
; I realized how complicated Cond is when it comes to this since I will need the helper functions made for expression. 
; Although And and other functions were made, I only used syntax-checker we made.
; I also added specs to my previous function kenneth and I made. 
; And finished more basic functions.

; 4/30/25 - Hamim (Comments Below)
; Cleaning up code, making sure test cases all run. In order to make the output look nicer, I added two (newline) so it is easier to see the output and what
; section of code corresponds to what.


; 4/30/25 - Alexis (Comments Below)
; I implemented some finishing touches to 1.1 for we can present the code to the professor tomorrow. 
; I also cleaned up 1.2 file and added some specs we missed. 
; Fixed some errors as well.


; 5/5/25 - Alexis (Comments Below)
; This was a very busy week due to exams and other projects for other classes. I spent most of today researching different kinds of proof
; such as structural, case, construction, etc. I also used the proofs the professor provided in class. 
; I then started practicing making the proofs for our code


; 5/7/25 - Alexis (Comments Below)
; I started working on section 1.5, and I opted to use structural induction. My thought process was this: to prove we implemented
; the TLS interpreter correctly, we will need to know the standard of correctness. We will also need to prove functions like 
; meaning, value, expression-to-action, etc. Overall making into one big proof for our interpreter. 


; 5/8/25 - Alexis (Comments Below)
; Today I collaborated with Hamim mostly. I worked on 1.1 specs since after our meeting with the professor, it was clear we needed a lot of improvements.
; Along with improving 1.6 and completing it with hamim. 
; I also worked on 1.5 today making proofs for other functions in 1.1. 


; 5/8/25 - Hamim (Comments Below)
; So today was the first day that I was able to work on this for a while because I had exams + projects for other classes. However, I spent all day today working on
; two things. During our last interview (interview 1), professor told me to add more test cases and essentially make them more complex. That is what I did today, I
; was able to add test cases for all functions and made sure that they were fairly complex. The second thing I completed was Section 1.6 of the project. I worked with
; Alexis on this part.


; 5/9/25 - Hamim (Comments Below)
; Today's goal is to organize the interpreter so that the functions can all run (they all do, but it does not look organized). Also, today is fixing the specs, and adding
; more specs to each function. Alexis will also be joining in doing some of the specs and the pre/post conditions, and proofs.


; 5/11/25 - Hamim (Comments Below)
; Today I was able to fix the pre and post conditions for certain functions that I just didn't know how to word properly. I was also able to complete the build function because
; I had it set up in the wrong way. I double checked all the test cases that Professor gave us, the ones from the book, and the ones i created, and they all work and return
; the correct answer.


; 5/12/25 - Hamim (Comments Below)
; Cleaned up the wording and examples for Section 1.6 of the project. Pushed code to Github on a separate file. 
