/* FORMAL TYPE DEFINITIONS HERE - never used (apart from equality types), just for the specification */

/* base_types */
type(tint).
type(tbool).

/* type_variables */
type(typevar(_)).

/* arrow_types */
type(arrow(T1, T2)) :-
    type(T1),
    type(T2).

/* tuple_types: implemented as lists */
type([]).
type([T1 | L]) :-
    type(T1),
    type(L).

/* equality_types: checking whether the types can have equality defined on them; these types are tint or tbool or tuples of types which have equality defined on them */
equality_type(tint).
equality_type(tbool).
equality_type(tuple([])).
equality_type(tuple([A | L])) :-
    equality_type(A),
    equality_type(tuple(L)).

/* FORMAL EXPRESSION DEFINITIONS_HERE - never used, just for the specification */

/* variable */
expr(var(_)).

/* integer_constant */
expr(X) :-
    integer(X).

/* bool_constant */
expr(true).
expr(false).

/* integer_ops */
expr(add(X, Y)) :-
    expr(X), expr(Y).

expr(sub(X, Y)) :-
    expr(X), expr(Y).

/* bool_ops */

expr(and(X, Y)) :-
    expr(X), expr(Y).

expr(or(X, Y)) :-
    expr(X), expr(Y).

expr(not(X, Y)) :-
    expr(X), expr(Y).

/* DEFINITIONS_DEFINITIONS_HERE */

/* helper functions for set implemented using list */

/* Note that all cuts here are green cuts, and are only for efficiency reasons*/

/* contains(A, B) checks whether A contains the element B */
contains([], _) :- fail.
contains([X | _], X) :- !.
contains([_ | Y], X) :- contains(Y, X).

intersects([], _) :- fail.
intersects([Y | _], X) :- contains(X, Y), !.
intersects([_ | YS], X) :- intersects(YS, X).

/* augment(L1, L2, L3) means L3 = L1[L2], so we join L1 and L2 in such a manner that L2 comes before L1 */
augment(L1, [], L1).
augment(L1, [X | XS], [X | YS]) :-
    augment(L1, XS, YS).

/* TYPE CHECKING STARTS. hastype(Gamma, E, T) type-checks the expression E with type T */

/* variables */
hastype(Gamma, var(X), T) :-
    contains(Gamma, (var(X), T)).

/* constants */
hastype(_, X, tint) :-
    integer(X).
hastype(_, true, tbool).
hastype(_, false, tbool).

/* integer_ops */
hastype(Gamma, add(X, Y), tint) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, sub(X, Y), tint) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, mul(X, Y), tint) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, div(X, Y), tint) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, mod(X, Y), tint) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).

/* boolean_ops */
hastype(Gamma, and(X, Y), tbool) :-
    hastype(Gamma, X, tbool),
    hastype(Gamma, Y, tbool).
hastype(Gamma, or(X, Y), tbool) :-
    hastype(Gamma, X, tbool),
    hastype(Gamma, Y, tbool).
hastype(Gamma, not(X, Y), tbool) :-
    hastype(Gamma, X, tbool),
    hastype(Gamma, Y, tbool).

/* int_comparison */
hastype(Gamma, lt(X, Y), tbool) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, le(X, Y), tbool) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, ge(X, Y), tbool) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).
hastype(Gamma, gt(X, Y), tbool) :-
    hastype(Gamma, X, tint),
    hastype(Gamma, Y, tint).

/* equality: note that we check that equality can be defined on the corresponding type */
hastype(Gamma, eq(X, Y), tbool) :-
    hastype(Gamma, X, T),
    hastype(Gamma, Y, T),
    equality_type(T).

/* conditional */
hastype(Gamma, if_then_else(X, Y, Z), T) :-
    hastype(Gamma, X, tbool),
    hastype(Gamma, Y, T),
    hastype(Gamma, Z, T).

/* qualified_expressions */
hastype(Gamma, let_in_end(D, E), T) :-
    typeElaborates(Gamma, D, Gamma1),
    augment(Gamma, Gamma1, Gamma2),
    hastype(Gamma2, E, T).

/* function_abstractions */
hastype(Gamma, func_abstr(var(X), E), arrow(T1, T2)) :-
    hastype([(var(X), T1) | Gamma], E, T2).

/* function_application */
hastype(Gamma, func(E1, E2), T) :-
    hastype(Gamma, E1, arrow(TE, T)),
    hastype(Gamma, E2, TE).

/* n_tuple */
hastype(_, [], []).
hastype(Gamma, [A | B], [T1 | T2]) :-
    hastype(Gamma, A, T1),
    hastype(Gamma, B, T2).

/* projection: note that here I have not added support for dynamic projection; the reason is that type-checking is static. also the indexing must start at 1 */
hastype(Gamma, proj(A, B), T) :-
    integer(B),
    hastype(Gamma, A, T1),
    nth1(B, T1, T).

/* TYPE ELABORATION STARTS typeElaborates(Gamma, D, Gamma1) considers the declaration D and carries out type elaboration and turns Gamma into Gamma1 */

dv(simple_def(var(X), _), [var(X)]).
dv(seq_def(D1, D2), DV) :-
    dv(D1, DV1),
    dv(D2, DV2),
    augment(DV2, DV1, DV).
dv(par_def(D1, D2), DV) :-
    dv(D1, DV1),
    dv(D2, DV2),
    augment(DV2, DV1, DV).
dv(local_in_end(_, D2), DV) :-
    dv(D2, DV).

/* simple definition */
typeElaborates(Gamma, simple_def(var(X), E), [(var(X), T)]) :- 
    hastype(Gamma, E, T).

/* sequential definition */
typeElaborates(Gamma, seq_def(D1, D2), Gamma100) :-
    typeElaborates(Gamma, D1, Gamma1),
    augment(Gamma, Gamma1, Gamma2),
    typeElaborates(Gamma2, D2, Gamma3),
    augment(Gamma1, Gamma3, Gamma100).

/* parallel definition - need to ensure that the defined variables do not have a non-empty intersection - so check that*/
typeElaborates(Gamma, par_def(D1, D2), Gamma100) :-
    dv(D1, DV1),
    dv(D2, DV2),
    \+ intersects(DV1, DV2),
    typeElaborates(Gamma, D1, Gamma1),
    typeElaborates(Gamma, D2, Gamma2),
    augment(Gamma1, Gamma2, Gamma100).

/* local definition */
typeElaborates(Gamma, local_in_end(D1, D2), Gamma100) :-
    typeElaborates(Gamma, D1, Gamma1),
    augment(Gamma, Gamma1, Gamma2),
    typeElaborates(Gamma2, D2, Gamma100).

