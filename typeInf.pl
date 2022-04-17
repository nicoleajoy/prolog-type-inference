:- dynamic gvar/2.
:- dynamic lvar/2.

% find type of expression
typeExp(X, int) :- integer(X).
typeExp(X, float) :- float(X).
typeExp(X, bool) :- typeBoolExp(X).

/* match functions by unifying with arguments
    and infering the result
*/
typeExp(Fct, T) :-
    \+ var(Fct), /* make sure Fct is not a variable */ 
    \+ atom(Fct), /* or an atom */
    functor(Fct, Fname, _Nargs), /* ensure we have a functor */
    !, /* if we make it here we do not try anything else */
    Fct =.. [Fname|Args], /* get list of arguments */
    append(Args, [T], FType), /* make it look like a function signature */
    functionType(Fname, TArgs), /* get type of arguments from definition */
    typeExpList(FType, TArgs). /* recurisvely match types */

% local variables
typeExp(Lvar, T) :-
    atom(Lvar),
    lvar(Lvar, T).
% global variables
typeExp(Gvar, T) :-
    atom(Gvar),
    gvar(Gvar, T).

/* propagate types */
typeExp(T, T).

/* list version to allow function mathine */
typeExpList([], []).
typeExpList([Hin|Tin], [Hout|Tout]):-
    typeExp(Hin, Hout), /* type infer the head */
    typeExpList(Tin, Tout). /* recurse */

% comparison
hasComparison(int).
hasComparison(float).
hasComparison(string).
% add
hasAdd(int).
hasAdd(float).
% sub
hasSub(int).
hasSub(float).
% mult
hasMult(int).
hasMult(float).
% div
hasDiv(int).
hasDiv(float).
% equal
hasEq(int).
hasEq(float).
hasEq(string).
% not equal
hasNEq(int).
hasNEq(float).
hasNEq(string).
% greater than
hasGT(int).
hasGT(float).
% greater than or equal
hasGTEq(int).
hasGTEq(float).
% lesser than
hasLT(int).
hasLT(float).
% lesser than or equal
hasLTEq(int).
hasLTEq(float).

/* predicate to infer types for boolean expressions */
typeBoolExp(true).
typeBoolExp(false).

typeBoolExp(X = Y) :- 
    typeExp(X, T),
    typeExp(Y, T),
    hasComparison(T),
    hasEq(X, T),
    hasEq(Y, T).
typeBoolExp(X \= Y) :- 
    typeExp(X, T),
    typeExp(Y, T),
    hasComparison(T),
    hasNEq(X, T),
    hasNEq(Y, T).
typeBoolExp(X > Y) :- 
    typeExp(X, T),
    typeExp(Y, T),
    hasComparison(T),
    hasGT(X, T),
    hasGT(Y, T).
typeBoolExp(X < Y) :- 
    typeExp(X, T),
    typeExp(Y, T),
    hasComparison(T),
    hasLT(X, T),
    hasLT(Y, T).

/* sum types
    typeSums :: X -> int 
    typeSums :: X -> float
*/
typeSums(X, Y, T) :-
    typeSum(Y, T),
    asserta(gvar(X, T)).
    % typeExp(X,T),
    % typeExp(Y,T).

% typeSum(_X, _Y, _T).
typeSum(X, Y) :-
    not(X=Y).

/* tuple types
    typeTuple(tuple(X,Y),(T, R)):-
*/
typeTuple(tuple(X, Y, Z), T, R, S):-
    typeExp(X, T),
    typeExp(Y, R),
    typeExp(Z, S),
    asserta(gvar(X, T)).

/* TODO: add statements types and their type checking */

typeStatement(X, T) :-
    typeExp(X, T).

/* local variable definition
    Example:
        lvLet(v, d, T, c) ~ let v = 3 in ...;
*/
typeStatement(lvLet(Name, Def, VarT, Code), T):-
    atom(Name), /* make sure we have a bound name */
    typeExp(Def, VarT), /* infer the type of var def and ensure it is VarT */
    bType(VarT), /* make sure we have an inferred type */
    asserta(lvar(Name, VarT)), /* add definition to database */
    typeCode(Code, T), % code type
    retract(lvar(Name, VarT)), % deassert lvar and pop from local database
    asserta(lvar(Name, VarT) :- false()), % clean wipe
    bType(T). % make sure that the type of the block is a valid type

/* global variable definition
    Example:
        gvLet(v, T, int) ~ let v = 3;
*/
typeStatement(gvLet(Name, T, Code), unit):-
    atom(Name), /* make sure we have a bound name */
    typeExp(Code, T), /* infer the type of Code and ensure it is T */
    bType(T), /* make sure we have an infered type */
    asserta(gvar(Name, T)). /* add definition to database */

/* global function definition
    Example:
        let add x y = x + y;
*/
typeStatement(gfLet(Name, Args, T, Code), T):-
    atom(Name), /* make sure we have a bound name */
    typeExp(Code, T), /* infer the type of Code and ensure it is T */
    is_list(Args), /* make sure Args is a list */
    append(Args, [T], X), /* append return type to Args */
    asserta(gvar(Name, X)). /* add definition to database */

/* if statements are encodes as:
    if(condition:Boolean, trueCode: [Statements], falseCode: [Statements])
*/
typeStatement(if(Cond, TrueB, FalseB), T) :-
    typeBoolExp(Cond),
    typeCode(TrueB, T),
    typeCode(FalseB, T).

% for statements Haskell
typeStatement(where(Name, Cond, Code), T):-
    typeBoolExp(Cond),
    atom(Name), /* make sure we have a bound name */
    typeExp(Code, T), /* infer the type of Code and ensure it is T */
    asserta(gvar(Code, T)). /* add definition to database */

/* Code is simply a list of statements. The type is 
    the type of the last statement 
*/
typeCode([S], T):-typeStatement(S, T).
typeCode([S, S2|Code], T):-
    typeStatement(S,_T),
    typeCode([S2|Code], T).

/*
% code blocks
typeCode(Code, T),
    typeExp(X, T).
    asserta(gvar(Code)),
    typeExp(Code, (T)), % infer type of Code and ensure it is T 
*/

/* Code is simply a list of expressions. The type is 
    the type of the last expression 
*/
typeCode([E], T):-typeExpList(E, T).
typeCode([E, E2|Code], T):-
    typeExpList(E,_T),
    typeCode([E2|Code], T).

/* top level function */
infer(Code, T) :-
    is_list(Code), /* make sure Code is a list */
    deleteGVars(), /* delete all global definitions */
    deleteLVars(), /* delete all local definitions */
    typeCode(Code, T).

/* Basic types
    TODO: add more types if needed
*/
bType(int).
bType(float).
bType(string).
bType(bool).
bType(unit). /* unit type for things that are not expressions */
/*  functions type.
    The type is a list, the last element is the return type
    E.g. add: int->int->int is represented as [int, int, int]
    and can be called as add(1,2)->3
*/
bType([H]):- bType(H).
bType([H|T]):- bType(H), bType(T).

/*
    TODO: as you encounter global variable definitions
    or global functions add their definitions to 
    the database using:
        asserta( gvar(Name, Type) )
    To check the types as you encounter them in the code
    use:
        gvar(Name, Type) with the Name bound to the name.
    Type will be bound to the global type
    Examples:
        g

    Call the predicate deleveGVars() to delete all global 
    variables. Best wy to do this is in your top predicate
*/

deleteGVars() :-
    retractall(gvar), 
    asserta(gvar(_X,_Y):-false()).

deleteLVars() :-
    retractall(lvar),
    asserta(lvar(_X,_Y) :- false()).

/*  builtin functions
    Each definition specifies the name and the 
    type as a function type

    TODO: add more functions
*/

% convert types
fType(iToFloat, [int, float]).
fType(fToInt, [float, int]).
% add
fType(iplus, [int, int, int]).
fType(fplus, [float, float, float]).
fType((+), [T, T, T]) :- hasAdd(T).
% sub
fType(iminus, [int, int, int]).
fType(fminus, [float, float, float]).
fType((-), [T, T, T]) :- hasSub(T).
% mult
fType(imult, [int, int, int]).
fType(fmult, [float, float, float]).
fType((*), [T, T, T]) :- hasMult(T).
% div
fType(idiv, [int, int, int]).
fType(fdiv, [float, float, float]).
fType((/), [T, T, T]) :- hasDiv(T).
% equal
fType(ieq, [int, int, int]).
fType(feq, [float, float, float]).
fType(seq, [string, string, string]).
fType((==), [T, T, T]) :- hasEq(T).
% not equal
fType(ineq, [int, int, int]).
fType(fneq, [float, float, float]).
fType(sneq, [string, string, string]).
fType((/=), [T, T, T]) :- hasNEq(T).
% greater than
fType(igt, [int, int, int]).
fType(fgt, [float, float, float]).
fType((>), [T, T, T]) :- hasGT(T).
% lesser than
fType(ilt, [int, int, int]).
fType(flt, [float, float, float]).
fType((<), [T, T, T]) :- hasLT(T).
% simple print
fType(print, [_X, unit]).

/* Find function signature
   A function is either built in using fType or
   added as a user definition with gvar(fct, List)
*/

% Check the user defined functions first
functionType(Name, Args):-
    gvar(Name, Args),
    is_list(Args). % make sure we have a function not a simple variable

functionType(Name, Args):-
    lvar(Name, Args),
    is_list(Args). % make sure we have a function not a simple variable    

% Check first built in functions
functionType(Name, Args) :-
    fType(Name, Args), !. % make deterministic

% This gets wiped out but we have it here to make the linter happy
gvar(_, _) :- false().
lvar(_, _) :- false().
