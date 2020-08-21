The last line in the assignment specification is as follows:

Note that this checker can work as a type inference engine.  However it does not work for polymorphic type inference.  Show with counter-examples that this is the case.

The reason for this is as follows.
Consider the program:

let id x = x in (id 1), (id true), (id []);;

In this program, id should have been a polymorphic function, and the value of the above expression should have been (1, true). However, with the checker implemented as a part of the assignment, the unification with the first application of id makes the checker deduce the type of id as int -> int, which then proceeds to fail on the second application of id. For polymorphic type inference, we need to make sure that the binding of the type happens to a copy of a function instead of the original copy itself or something else that prevents the fixing of the type of the function which is meant to be polymorphic.
