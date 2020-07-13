%% -*- mode: prolog; coding: utf-8 -*-

%% eval_decls(+Env, +Decls, -Res)
%% Évalue une liste de déclarations et renvoie dans Res l'expression finale.
eval_decls(Env, [Last], Res) :-
    !, print_message(debug('SF'), elaboratingMain(Last)),
    %% spy(eval),
    elaborate(Env, Last, Expanded),
    %% nospy(eval),
    print_message(debug('SF'), elaborated(Expanded)),
    check(Env, Expanded, T),
    print_message(debug('SF'), type_is(T)),
    eval(Env, Expanded, Res).
eval_decls(Env, [Decl | Decls], Res) :-
    print_message(debug('SF'), elaborating(Decl)),
    elaborate(Env, Decl, Expanded),
    print_message(debug('SF'), elaborated(Expanded)),
    eval_decl(Env, Expanded, NewEnv),
    print_message(debug('SF'), processed(Decl)),
    eval_decls(NewEnv, Decls, Res).

eval_decl(Env, X : T, NewEnv) :-                            %% aide inférence type ou définition récursive
    atom(X),
    %% spy(check),
    %% elaborate(Env, T, TE),
    print_message(debug('SF'), declare(X,T)),
    check(Env, T, type), NewEnv = [(X,T,forward) | Env].    %% nom, type, définition
eval_decl(Env, define(X, E), NewEnv) :-
    atom(X),
    print_message(debug('SF'), defining(X)),
    (lookup(Env, X, T, forward) ->
         %% spy(check),
         check(Env, E, T);
     print_message(debug('SF'), checking(X)),
     check(Env, E, T)),
    print_message(debug('SF'), define(X, T)),
    NewEnv = [(X,T,V) | Env],                               %% V est résultat de l'évaluation
    eval(Env, E, V).                                        %% ordre inverse important pour définitions récursives

%% lookup(+Env, +Var, -Type, -Val)
%% Renvoie le type (et la valeur) de Var dans Env.
lookup(Env, X, T, V) :- member((X, T1, V1), Env), !, T1 = T, V1 = V.


%% remove(+X, +List, -Res)
%% Renvoie une liste Res identique à List, sauf avec X en moins.
remove(_, [], []).
remove(X, [X|YS], ZS) :- !, remove(X, YS, ZS).
remove(X, [Y|YS], [Y|ZS]) :- remove(X, YS, ZS).

%% union(+Set1, +Set2, -Set)
%% Renvoie l'union de deux sets.  Si ni Set1 ni Set2 n'ont de duplicats, alors
%% le résultat n'en aura pas non plus.
union([], YS, YS).
union(XS, [], XS).
union([X|XS], YS, ZS) :-
    union(XS, YS, S),
    (member(X, YS) -> ZS = S; ZS = [X|S]).

%% freevars(+Exp, -Freevars)
%% Renvoie les variables libres de Exp.
freevars(N, []) :- number(N).
freevars(DontCare, []) :- var(DontCare), !.
freevars(quote(_), []).
freevars(X, [X]).
freevars(X, [X]) :- atom(X).
freevars(forall(X, T), FVs) :-
    freevars(T, FV), remove(X, FV, FVs).
freevars(fn(X, E), FVs) :-
    freevars(E, FV), remove(X, FV, FVs).
freevars(tfn(X, E), FVs) :-
    freevars(E, FV), remove(X, FV, FVs).
%% Pour n'importe quel autre terme composé (genre "app(E1, E2)"), applique
%% freevars récursivement sur ses arguments.
freevars([[]], []) :- !.
freevars(E, FV) :-
    E =.. [_|[Arg|Args]],
    freevars(Arg, FVa),
    freevars(Args, FVas),
    union(FVa, FVas, FV).


%% subst(+Exp, +Var, +Val, -NewExp)
%% Renvoie la substitution de Var par Val dans Exp.
subst(Exp, X, V, NewExp) :- freevars(V, FV), subsT(Exp, X, V, FV, NewExp).
%% subsT(+Exp, +Var, +Val, +FVval, -NewExp)
%% Prédicat auxiliaire interne à "subst".
subsT(X, _, _, _, X) :- var(X), !.
subsT(X, X, V, _, V) :- !.
subsT(X, Y, _, _, X) :- atomic(X), !, X \= Y.
subsT(quote(V), _, _, _, quote(V)).
subsT(Fn, Y, V, FV, Exp) :-
    (Fn = fn(_, _); Fn = tfn(_, _); Fn = forall(_,_)),
    !,
    Fn =.. [Head,X,E],
    (member(X, FV), freevars(E, FVe), member(Y, FVe) ->
         %% V fait référence à un autre X et Y apparaît dans E: appliquer le
         %% renommage α et ressayer pour éviter la capture de nom.
         new_atom(X, NewX),
         subsT(E, X, NewX, [NewX], NewE),
         subsT(NewE, Y, V, FV, NewerE),
         Exp =.. [Head,NewX,NewerE];
     X = Y ->
         %% Y est caché par X.
         Exp = Fn;
     subsT(E, Y, V, FV, Es),
     Exp =.. [Head,X, Es]).
%% Pour n'importe quel autre terme composé (genre "app(E1, E2)"), applique
%% subsT récursivement sur ses arguments.
subsT([[]], _, _, _, [[]]) :- !.
subsT(E, Y, V, FV, Exp) :-
    E =.. [Head|[Arg|Args]],
    subsT(Arg, Y, V, FV, NewArg),
    subsT(Args, Y, V, FV, NewArgs),
    Exp =.. [Head|[NewArg|NewArgs]].
subsT(E, Y, V, FV, _) :-
    print_message(error, subsT_error(E, Y, V, FV)),!.

check_type(T1, T2) :-
    T1 = T2 -> true;
    print_message(error, type_mismatch(T1, T2)), fail.

%% check(+Env, +Exp, ?Type)
%% Vérifie/infère le type d'une expression.  Utilisé aussi pour vérifier
%% si une expression de type est valide.
check(Env, X, T1) :- atom(X), lookup(Env, X, T2, _), !, check_type(T1, T2), !.
check(_, N, int) :- number(N), !.

% check(Env, macro(Exp), list(sexp) -> sexp).
check(Env, app(macro,_), macroexpander) :- !.

% check(Env, app(app(tapp(map,?),tapp(car,?)),E), list(int)) :- !.

%% 3
check(Env, if(E,E1,E2), T) :-
    % print_message(debug('check'), checking(if(E,E1,E2))),
    (lookup(Env, E, _, temp) -> true; check_type(T_E, bool)),
    (lookup(Env, E1, _, temp) -> true; check_type(T1, T)),
    (lookup(Env, E2, _, temp) -> true; check_type(T_E2, T)),
    (lookup(Env, E1, T_, temp), lookup(Env, E2, T, temp) -> T = T_; true),
    check(Env, E, T_E), check(Env, E1, T1), check(Env, E2, T_E2), !.

    % check_type(T_E, bool), check_type(T1, T), check_type(T_E2, T),
    % check(Env, E, T_E), check(Env, E1, T1), check(Env, E2, T_E2), !.

%% 4
check(Env, fn(X,E), T) :-
    lookup(Env,X,_,_) , ! -> %%type et val?
        % print_message(debug('a'),check_fn_tfn()),
        check(Env, E, T_E);
        % print_message(debug('a'),check_fn()),
        NewEnv = [(X,X,temp)|Env], check(NewEnv, E, T_E), !,
        print_message(debug('a'),fn_exp(T_E)),
        T = forall(X,X -> T_E).




%% 5
% check(Env, app(tapp(E1,_),E2), T) :-
%     check(Env, E2, T_E2),
%     % print_message(debug('check'),app_tapp(Env)),
%     lookup(Env, E1, forall(A,T2), _), !,
%     % lookup(Env, E1, X, _), !,
%     subst(T2,A,T_E2,T), !.


% check(Env, app(E1,E2), T2) :-
%     print_message(debug('check'), checling(app(E1,E2))),
%     atom(E2), (lookup(Env, E, _, temp), ! ->
%         check(Env, E1, T1 -> T2), !;
%         check(Env, E2, T1), !, check(Env, E1, T1 -> T2), !), !.


% t ::= ct | list(t) | t1 -> t2 | a | forall(a,t)

% check(Env, app(E1,E2), T) :-
%     print_message(debug('check'), checling(app0(app(E1,E2)))),
%     check(Env, E2, T1),!, check(Env, E1, T1 -> forall(X,E)),!,
%     T = forall(X,E),
%     print_message(debug('check'), checling(app(E1,E2))).

% check(Env, app(E1,E2), T2) :-
check(Env, app(X,E), T) :-
    lookup(Env, X, ((list(sexp)->sexp) -> macroexpander), V), !, T = macroexpander.


check(Env, app(E1,tapp(E2,?)), T2) :-
    print_message(debug('g'),debut_tapp_droite(app(E1,tapp(E2,?)))),

    check(Env,E1,T1 -> T2), !,
    print_message(debug('g'),type_debug_T(T1 -> T2)).

check(Env, app(tapp(E1,?),E2), T2) :-
    print_message(debug('g'),debut_tapp_gauche(app(tapp(E1,?),E2))),

    check(Env,E2,T1), !,
    % print_message(debug('g'),type_T1(T1)),
    check(Env, tapp(E1,T1), T), !,

    % print_message(debug('g'),type_T1versT2(T)),
    check_app(Env, T,T1,T2_), !,
    % print_message(debug('g'),type_final(T2_)),
    T2 = T2_.

check(Env, app(app(tapp(A,?),tapp(B,?)),E), T) :-
    print_message(debug('g'),type___(E)),
    check(Env,E,T1), !,
    print_message(debug('g'),type___T1(T1)),

    check(Env, tapp(B,?), TypeB),
    print_message(debug('g'),typeB_(TypeB)),

    check(Env, tapp(A,?), TypeA),
    print_message(debug('g'),typeA_(TypeA)),

    check(Env, tapp(B,?), TTB),
    check(Env, tapp(A,TTB), TAA_),
    check_app(Env, TAA_, TTB, TAA),
    print_message(debug('g'),type__Test(TAA)),

    
    % check(Env, tapp(B,T1), T_B), !,
    % print_message(debug('g'),type___TB(T_B)),

    % print_message(debug('g'),type_T1versT2(T)),
    % check_app(Env, T_B,T1,T2), !,
    print_message(debug('g'),type___T2(T2)),


    check(Env, tapp(A,T2), T_), !,
    check_app(Env, TAA,T1,T__), !,
    print_message(debug('g'),type_final(T__)),
    T = T__.


check(Env, app(E1,E2), T2) :-
    check(Env,E2,T1), !, check(Env, E1, T), !,
    check_app(Env, T,T1,T2_), !, T2 = T2_.


%% 6
check(Env, tfn(A,fn(X,E)), forall(A, A -> T_)) :-
    print_message(debug('f'),debut_tfn(E)),
    NewEnv = [(X,A,type)|Env], check(NewEnv, E, T_), !,
    print_message(debug('f'),fin_tfn(E,T_)).


% check(Env, tfn(A,tfn(B,E)), forall(A, forall(BT))) :-
check(Env, tfn(A,E), forall(A, T)) :-
    print_message(debug('f'),debut_tfn(E)),
    NewEnv = [(A,A,type)|Env], check(NewEnv, E, T_), !,
    print_message(debug('f'),fin_tfn(E,T_)), T = T_.



%% 7
check(Env, tapp(E,T1), T) :-
    lookup(Env, E, forall(A,T2), _), !,
    subst(T2,A,T1,P), !, 
    T = P.

%% 8
check(_, quote(_), sexp).

%% 9
check(Env, list(T), type) :- check(Env, T, type), !.

%% 10
check(Env, T1 -> T2, type) :- check(Env, T1, type), check(Env, T2, type), !.

%% 11
check(Env, forall(A,T), type) :-
    NewEnv = [(A,type,type)|Env], check(NewEnv, T, type), !.

check(_,E,_) :- print_message(error, check_error(E)), fail.




check_app(_, forall(X,E), T1, T) :- subst(E,X,T1,T2), !, T = T2.


check_app(Env, T1 -> forall(X,E), T1_, T) :- subst(E, X, T1_, T), !.

check_app(Env, T1 -> T2, T1_, T) :-
    lookup(Env, T1_, _, V) ->
        T = T2, !.
   
check_app(_,E,T1,T) :- E = (T1 -> T2), T = T2.

check_app(_,E,list(X),T) :-
    E = (list(X_) -> T2), check_sub(X,X_,T2,T).

check_app(_,(list(sexp) -> sexp),_,sexp).
check_app(_,macroexpander,_,macroexpander).

check_app(_,E,T,_) :- print_message(error,error_check_app(E,T)), fail.


check_sub(X,Y,T2,T) :-
    X = list(X_), Y = list(Y_), check_sub(X_,Y_,T2,T).

check_sub(X,Y,T2,T) :- subst(T2,Y,X,T).

%% elaborate(+Env, +Exp, -NewExp)
%% Renvoie la version expansée de Exp, ce qui inclus:
%% - expansion de macros.
%% - expansion du sucre syntaxique fun(arg1, arg2, ...).
%% - ajout des instantiations de types.

args_to_sexp([Arg|[]], NewArg) :-
    NewArg = cons(quote(Arg), nil).

args_to_sexp([Arg|Args], NewArg) :-
    args_to_sexp([Arg], Arg_),!, args_to_sexp(Args,Args_),!,
    NewArg = cons(quote(Arg), Args_).

    
elaborate(_, Exp, Exp) :- number(Exp).

elaborate(Env, Exp, NewExp) :-
    Exp =.. [Head|Args], Head \= macro,
    lookup(Env,Head, macroexpander,V) ->
    args_to_sexp(Args,Args_),
    NewExp_ = app(V,Args_),
    elaborate(Env,NewExp_,NewExp0),
    eval([(args,sexp,args)|Env],NewExp0,NewExp1),
    elaborate(Env,NewExp1,NewExp).


%% list
elaborate(Env, list(T), list(T_)) :-
    elaborate(Env, T, T_), !.

%% define
elaborate(Env, define(X,E), define(X,E_exp)) :-
    elaborate(Env, E, E_exp), !.

%% définition de type
elaborate(_, X : T, X : T) :- !.

%% app
elaborate(Env, app(E1,E2), app(E1_,E2_)) :-
    elaborate(Env, E1, E1_), !, elaborate(Env, E2, E2_), !.

%% fn
elaborate(Env, fn(E1,E2), fn(E1_,E2_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.

%% quote
elaborate(Env, quote(E), quote(E)).

%% if
elaborate(Env, if(E1,E2,E3), if(E1_,E2_, E3_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), elaborate(Env, E3, E3_), !.

%% tfn
elaborate(Env, tfn(E1,E2), tfn(E1_,E2_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.

%% tapp
elaborate(Env, tapp(E1,E2), tapp(E1,E2)).


elaborate(Env, Exp, NewExp) :-
    atom(Exp), lookup(Env, Exp, forall(_,_), _), ! ->
        NewExp = tapp(Exp,?).

elaborate(_, Exp, Exp) :- atom(Exp).

%% fonction type polymorphe
elaborate(Env, Exp, NewExp) :-
    Exp =.. [Head|Args], Args = [E1|ES], elaborate(Env, E1, E1_),
    (lookup(Env, Head, forall(_,_), V), ! ->
        elim_suc(Env, app(tapp(Head,?), E1_), ES, NewExp);
        elim_suc(Env, app(Head, E1_), ES, NewExp)), !.




elim_suc(_, Exp, [], Exp). %% :- print_message(debug(''),fin_elim(Exp)), !.
elim_suc(Env, Exp, [E|ES], NewExp) :-
    (elaborate(Env, E, NewE) ->
        (lookup(Env, NewE, forall(_,_), V) ->
            elim_suc(Env, app(Exp, tapp(NewE,?)), ES, NewExp), !;
            elim_suc(Env, app(Exp, NewE), ES, NewExp) ,!);
        (lookup(Env, E, forall(_,_), _) ->
            elim_suc(Env, app(Exp, tapp(E,?)), ES, NewExp), !;
            elim_suc(Env, app(Exp, E), ES, NewExp) ,!)).


%% apply(+Fun, +Arg, -Val)
%% Evaluation des fonctions et des opérateurs prédéfinis.
apply(closure(X, Env, Body), Arg, V) :- eval([(X, _, Arg)|Env], Body, V).
apply(builtin(BI), Arg, V) :- builtin(BI, Arg, V).
%% builtin(list, V, list(V)).
builtin(macro, V, macro(V)).
builtin(compoundp, V, Res) :- compound(V) -> Res = true; Res = false.
builtin(makenode, Head, builtin(makenode(Head))) :- atom(Head).
builtin(makenode(Head), Args, V) :- V =.. [Head|Args].
builtin((+), N1, builtin(+(N1))).
builtin(+(N1), N2, N) :- N is N1 + N2.
builtin(car, [X|_], X).
builtin(cdr, [_|XS], XS).
builtin(cdr, [], []).
builtin(empty, X, Res) :- X = [] -> Res = true; Res = false.
builtin(cons, X, builtin(cons(X))).
builtin(cons(X), XS, [X|XS]).

%% eval(+Env, +Exp, -Val)
%% Évalue Exp dans le context Env et renvoie sa valeur Val.
eval(_, app(macro,V), V) :- !.
eval(_, N, N) :- number(N), !.
eval(Env, X, V) :-
    atom(X), !,
    (lookup(Env, X, _, V), !;
     print_message(error, unknown_variable(X)), fail).
eval(_, quote(V), V) :- !.
eval(Env, fn(X, E), closure(X, Env, E)) :- !.
eval(Env, tfn(_, E), V) :- !, eval(Env, E, V).
eval(Env, tapp(E, _), V) :- !, eval(Env, E, V).
eval(Env, if(E1, E2, E3), V) :-
    !, eval(Env, E1, V1),
    (V1 = true -> eval(Env, E2, V);
     eval(Env, E3, V)).
eval(Env, app(E1, E2), V) :-
    !, eval(Env, E1, V1),
    eval(Env, E2, V2),
    apply(V1, V2, V).
eval(_, E, _) :-
    print_message(error, unknown_expression(E)), fail.

%% env0(-Env)                                                       %% défini les types builtin
%% Renvoie l'environnment initial qui défini les types des primitives
%% implémentées directement dans le langage et son évaluateur.
env0(Env) :-
    Env = [(type, type, type),
           (sexp, type, sexp),                                  %% sexp = exp que recoivent les macros
           (int, type, int),
           ((+), (int -> int -> int), builtin(+)),
           (bool, type, bool),
           (true, bool, true),
           (false, bool, false),
           (compoundp, (sexp -> bool), builtin(compoundp)),
           (makenode, (sexp -> list(sexp) -> sexp), builtin(makenode)),
           (nil, forall(t, list(t)), []),
           (cons, forall(t, (t -> list(t) -> list(t))), builtin(cons)),
           (empty, forall(t, (list(t) -> bool)), builtin(empty)),
           (car, forall(t, (list(t) -> t)), builtin(car)),
           (cdr, forall(t, (list(t) -> list(t))), builtin(cdr)),
           (macroexpander, type, macroexpander),
           (macro, ((list(sexp) -> sexp) -> macroexpander), builtin(macro))].

%% pervasive(-Decls)
%% Renvoie un exemple de déclarations.
pervasive(
        % [define(zero, 0),
        %  define(zero_0, app(app(+, zero), zero)),
        %  define(id_int, fn(i, app(app(+, i), zero))),
        %  define(zero_1, app(id_int, zero)),
        %  identity : forall(t, (t -> t)),
        %  define(identity, tfn(t, fn(x,x))),
        %  define(zero_2, identity(zero)),
        %  zero_2+zero_1
         %% Pour pouvoir écrire "mklist(1,2,3)".
         [define(mklist,
                macro(fn(args,
                         makenode(quote(cons),
                                  cons(car(args),
                                       cons(if(empty(cdr(args)),
                                               quote(nil),
                                               makenode(quote(mklist),
                                                        cdr(args))),
                                            nil)))))),
        % mklist(car(args))
        %  %% Pas aussi pratique que quasiquote/unquote, mais quand même
        %  %% un peu mieux que just "makenode".
         define(makeqnode,
                macro(fn(args,
                         makenode(quote(makenode),
                                  mklist(makenode(quote(quote),
                                                  mklist(car(args))),
                                         makenode(quote(mklist),
                                                  cdr(args))))))),
        % makeqnode(+,quote(1),quote(2))
        % mklist(1,2,3,4,5) 
        %  %% Pour pouvoir définir ses macros avec "defmacro(name,args,e)".
         define(defmacro,
                macro(fn(args,
                         makeqnode(define,
                                   car(args),
                                   makeqnode(macro,
                                             makenode(quote(fn),
                                                      cdr(args))))))),
        %  %% Pour pouvoir définir ses variables avec "X = E" plutôt qu'avec
        %  %% "define".
         defmacro(=, args, makenode(quote(define),args)),
        %  %% Les déclarations offrent un sorte de "let" récursif global,
        %  %% et cette macro-ci offre un "let(x,e1,e2)" pour ajouter une
        %  %% déclaration locale.
         defmacro(let, args,
                  makeqnode(app,
                            makeqnode(fn, car(args), car(cdr(cdr(args)))),
                            car(cdr(args)))),
         %% Notre bonne vieille fonction "map", qui a besoin d'une
         %% déclaration de type, vu qu'elle est récursive.
         map : forall(a, forall(b, ((a -> b) -> list(a) -> list(b)))),
         map = tfn(a, tfn(b, fn(f, fn(xs,
                                      if(empty(xs),
                                         nil,
                                         cons(f(car(xs)), map(f,cdr(xs)))))))),
        defmacro(test,x,makenode(quote(true),nil)),
        map(car, cons(cons(1,nil),cons(cons(3,cons(2,nil)),nil)))
        % test(1)
        % mklist(1,2,3)

    ]).

%% runraw(+Prog, -Val)
%% Exécute programme Prog dans l'environnement initial.
runraw(P, V) :- env0(Env), eval_decls(Env, P, V).

%% run(+Prog, -Val)
%% Comme `runraw`, mais ajoute l'environnement "pervasive" défini ci-dessus.
run(P, V) :- env0(Env), pervasive(Per), append(Per, P, Code),
             eval_decls(Env, Code, V).
