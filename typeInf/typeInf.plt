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

% this test should fail
test(typeExp_iplus_F, [fail]) :-
    typeExp(iplus(int, int), float).

test(typeExp_iplus_T, [true(T == int)]) :-
    typeExp(iplus(int, int), T).

% NOTE: use nondet as option to test if the test is nondeterministic

% test for statement with state cleaning
test(typeStatement_gvar, [nondet, true(T == int)]) :- % should succeed with T=int
    deleteGVars(), /* clean up variables */
    typeStatement(gvLet(v, T, iplus(X, Y)), unit),
    assertion(X == int), assertion( Y == int), % make sure the types are int
    gvar(v, int). % make sure the global variable is defined

% same test as above but with infer 
test(infer_gvar, [nondet]) :-
    infer([gvLet(v, T, iplus(X, Y))], unit),
    assertion(T==int), assertion(X==int), assertion(Y=int),
    gvar(v,int).

% test custom function with mocked definition
test(mockedFct, [nondet]) :-
    deleteGVars(), % clean up variables since we cannot use infer
    asserta(gvar(my_fct, [int, float])), % add my_fct(int)-> float to the gloval variables
    typeExp(my_fct(X), T), % infer type of expression using or function
    assertion(X==int), assertion(T==float). % make sure the types infered are correct

% Test 1
test(simple_if, [nondet]) :-
    typeStatement( if(true, [3], [4]), T),
    assertion(T==int).

% Test 2
test(where_test, [nondet]) :-
    typeStatement(where(unit, true, bool), T),
    assertion(T==bool).

/*Tuple Types Test*/
test(tup_test,[nondet]) :-
    typeTuple(tuple(X,Y,Z), float,int,true),
    assertion(X==float),
    assertion(Y==int),
    assertion(Z==true).

/*Sum Types Test*/
test(sum_test,[fail]) :-
    typeSums(type, int, int),
    assertion(type==int),
    assertion(type==int).

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
