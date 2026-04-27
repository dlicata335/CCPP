This final homework, including the oral presentation of it to me, will
be worth 20% of your grade (recall that 70% is for the other homeworks,
and 10% for class participation). This homework is due on the last day
of the final exam period, Friday 5/15/26 at 5:00PM.  You will sign up to
present progress to me sometime during exams (Tuesday 5/12 through
Friday 5/15), but you can continue working on the homework after the
presentation.

Please refer to the
[syllabus](https://dlicata.wescreates.wesleyan.edu/teaching/ccpp-s26/policy.html)
for the course's interpretation of the honor code. This homework is
non-collaborative, so no collaboration between students is allowed.  No
assistance from any person or source, including online sources or
generative AI tools, is allowed, except the Professor and TAs.  Make
sure you have any generative AI-based VSCode plugins (Codex, Copilot)
turned off.  An exception is that, for problems below that say to "look
up" something, you can use any resources you want to learn about the
concept being formalized, as long as you do not search for or look at a
formalization of that concept in a proof assistant.  Similarly, if you
choose your own project, you can use any resources to learn about the
topic.  But any Agda code you hand in should be entirely your own, and
not derived from someone else's Agda code or code in a different proof
assistant.

# Possible homework topics

This homework is open-ended, and you can choose your own topic or one
from the list below.  Each student's homework will be graded based both
on how much you accomplish and how difficult the task is.  For the
suggested topics, my guess is that goals marked "easier" will be worth
around half to 3/4s of the goals marked "harder", but that is tentative
in case something turns out to be easier or harder than I expect.
Significant partial credit will be given for work in progress.

The proposed topics below list some extensions of homeworks we have done
this semester.

## Choosing your own topic

If you want to choose your own topic and formalize something about it in
Agda, please meet with me during one of the help sessions to discuss
what you want to do, whether it seems feasible, and how much progress
would be expected.

## Formalization of linear algebra

(Easier) Define a vector as a ListOfLength n as in [Lecture
13](https://github.com/dlicata335/CCPP/blob/main/lectures/Lect13.lagda.md).
Define an n x m matrix analogously as a type Matrix n m.  Define some
operations on vectors and matrices, such as addition, scaling, dot
product, and matrix multiplication.  Prove that matrix multiplication
defines a linear map, i.e. that M\*(v1 + v2) = M\*v1 + M\*v2 and M\*0 = 0.
You are welcome to look up whatever resources you want to learn or
remember linear algebra.

(Harder) Continue to more linear algebra of your choice.  

## Regular expressions

(Easier) Do the bonus problem from Homework 7, i.e. prove that the
exhaustive search based matcher is complete.  Add a complement operation
to regular expressions, where s is in the language of (not r) iff s is
not in the language of r, and implement the matcher for this.  

(Harder) Prove that the matcher from Homework 8 is complete, i.e. that
when it returns None, there is no splitting that into a front and a back
where the front is in the language of the regular expression and the
back is in the language of the stack.

(Harder) Look up "backreferences" in various languages' regexp
libraries, such as Perl.  The idea is that, if a regular expression
contains a capture [ r ], you can ask that a later part of the string
matches whatever string matched that group.  For example, the string
aaabaaa matches [a+]b\1 (where \1 is a backreference to the most recent
capturing group) because aaa matches a+, b matches b, and aaa matches \1
(because the portion of the string matching [a+] was aaa).  aaaba does
not match this regular expression.  Define when a string is in the
language of a regular expression containing a backreference (hint: you
might need to change the type of s ∈L r to add some extra data) and
write a certified matcher that handles backreferences in the style of either homework 7 or 8.
For simplicity you can start with a language that allows only a single
backreference to the most recent capturing group.  

## Binary search trees

(Easier) Combine your solution to Homework 8 with the ideas from
[Lecture
20](https://github.com/dlicata335/CCPP/blob/main/lectures/Lect20.lagda.md)
to prove that red-black tree insertion produces a sorted tree.  Prove
that prove that a key is in the result of insert iff it was in the
original tree or it is the newly inserted key.  

(Harder) Look up the definition of an AVL tree and the algorithm for
inserting into an AVL tree (or you can start from [this
code](https://dlicata.wescreates.wesleyan.edu/teaching/fp-s25/materials/lecture/lect21avl.sml)).
Define a type of AVL trees such that a value of that type satisfies the
depth invariants.  Prove that AVL tree insertion preserves this
invariant by defining an insert function for this type of AVL trees.

## Tactics

(Easier) Finish the tactics lab from [Lecture
23](https://github.com/dlicata335/CCPP/blob/main/lectures/Lect23-starter.lagda.md).

(Medium) Use the same ideas to write a tactic that solves inequalities
(<), and show how your tactic can prove some of the goals from Homework
7 like size r + length s < (1 + size r + size r2) + length s.  

(Medium) Extend the tactic implementation so that the Syntax can have
any number of variables, not just four. Hint: index the Syntax type by
the number of variables allowed (Syntax n means a term with n
variables), and use something like the "positions" from Homework 3 for
variables.  

(Harder) Extend the tactic implementation so that it can prove goals
involving *assumed* inequalities, such as "if x < y then a + x < a + y",
and use it to prove the goals from Homework 7 in which the length of the
string changes, like size r + length f < 1 + size r + size r2 + length s
where length f ≤ length s.  (The tactic does not need to prove length f
≤ length s --- this would be given to the tactic.)

# What to expect in the homework presentation

In the presentation, you will walk me through the code you have written
(a "codewalk").  I will ask questions about the code, and might ask you
to redo a bit of it or to prove something related.  The oral
presentation does not have a separate point value; it will be used to
help me assess your written handin.

