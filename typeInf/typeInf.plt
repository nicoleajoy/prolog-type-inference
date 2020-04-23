:- begin_tests(typeInf).
:- include(typeInf). 

/* Note: when writing tests keep in mind that 
    the use of of global variable and function definitions
    define facts for gvar() predicate. Either test
    directy infer() predicate or call
    delegeGVars() predicate to clean up gvar().
*/

% tests for typeExp

test(typeExp_iplus) :- 
    typeExp(iplus(int,int), int).

test(typeExp_iplus_T, [true(T == int)]) :-
    typeExp(iplus(int, int), T).

test(typeExp_iplus_F, [fail]) :-
    typeExp(iplus(int, int), float).

test(typeExp_fplus) :- 
    typeExp(fplus(float,float), float).

test(typeExp_fplus_T, [true(T == float)]) :-
    typeExp(fplus(float, float), T).

test(typeExp_fplus_F, [fail]) :-
    typeExp(fplus(float, float), int).

% NOTE: use nondet as option to test if the test is nondeterministic

% test for statement with state cleaning
test(typeStatement_gvar, [nondet, true(T == int)]) :- % should succeed with T=int
    deleteGVars(), /* clean up variables */
    deleteLVars(),
    typeStatement(gvLet(v, T, iplus(X, Y)), unit),
    assertion(X==int), assertion(Y==int), % make sure the types are int
    gvar(v, int). % make sure the global variable is defined

% same test as above but with infer 
test(infer_gvar, [nondet]) :-
    infer([gvLet(v, T, iplus(X, Y))], unit),
    assertion(T==int), assertion(X==int), assertion(Y=int),
    gvar(v,int).

% test custom function with mocked definition
test(mockedFct, [nondet]) :-
    deleteGVars(), % clean up variables since we cannot use infer
    deleteLVars(),
    asserta(gvar(my_fct, [int, float])), % add my_fct(int)-> float to the gloval variables
    typeExp(my_fct(X), T), % infer type of expression using or function
    assertion(X==int), assertion(T==float). % make sure the types infered are correct

/* test gvLet (global variables) */
test(gvLet_i, [nondet]) :- % assign global int variable
    deleteGVars(),
    deleteLVars(),
    typeStatement(gvLet(i, TAssign, iplus(int, int)), T),
    assertion(T==unit), assertion(TAssign==int).

test(gvLet_f, [nondet]) :- % asssign global float variable
    deleteGVars(),
    deleteLVars(),
    typeStatement(gvLet(i, TAssign, fplus(float, float)), T),
    assertion(T==unit), assertion(TAssign==float).

/* test lvLet (local variables) */
test(lvLet_i, [nondet]) :- % assign local int variable
    deleteGVars(),
    deleteLVars(),
    typeStatement(lvLet(v, iplus(int, int), int, [iplus(v,int)]), R),
    assertion(R==int).

test(lvLet_f, [fail]) :- % assign local float variable
    deleteGVars(),
    deleteLVars(),
    typeStatement(lvLet(v, fplus(X, Y), T, [bool]), unit),
    assertion(T==float), assertion(X==float), assertion(Y==float),
    lvar(v, infloatt).

/* test if statement */
test(if_test, [nondet]) :-
    typeStatement(if(true, [3], [4]), T),
    assertion(T==int).

/* test for statement */
test(where_test, [nondet]) :-
    typeStatement(where(unit, true, bool), T),
    assertion(T==bool).

/* infer tests */
test(infer_test1, [nondet]) :-
    infer([iplus(int,int), bool], bool).

test(infer_test2, [fail]) :-
    infer([iplus(int, int)], float).

test(infer_test3, [nondet]) :-
    infer([fplus(float,float)], float).

test(infer_test4, [fail]) :-
    infer([fplus(float, float)], int).

test(infer_test5, [nondet]) :-
    infer([gvLet(u, T1, iplus(_, _)),
           gvLet(v, T2, fplus(_, _)),
           iplus(u, int),
           fplus(v, float)], float),
    assertion(T1==int),
    assertion(T2==float).

test(infer_test6, [nondet]) :-
    infer([gvLet(u, T1, fplus(_, _)),
           gvLet(v, T2, iplus(_, _)),
           fplus(u, float),
           iplus(v, int)], int),
    assertion(T1==float),
    assertion(T2==int).

test(infer_test7, [fail]) :-
    infer([gvLet(u, T1, iplus(_, _)),
           gvLet(v, T2, fplus(_, _)),
           fplus(u, int),
           iplus(v, float)], float),
    assertion(T1==int),
    assertion(T2==memory_file_to_atom('Param1', 'Param2')).

:-end_tests(typeInf).
