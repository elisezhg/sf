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

check_type(T1, T2) :-
    T1 = T2 -> true;
    print_message(error, type_mismatch(T1, T2)), fail.

%% check(+Env, +Exp, ?Type)
%% Vérifie/infère le type d'une expression.  Utilisé aussi pour vérifier
%% si une expression de type est valide.
check(Env, X, T1) :- atom(X), lookup(Env, X, T2, _), !, check_type(T1, T2), !.
check(_, N, int) :- number(N), !.


%% remplace les ? par le bon type
check(Env, app(tapp(X,?),E), T) :-
    print_message(debug('a'),checking()),
    check(Env, E, T_E), !, check(Env, app(tapp(X,T_E),E), T), !,
    print_message(debug('a'),here(app(tapp(X,T_E),E))).

check(Env, app(E,tapp(X,?)), T) :-
    check(Env, E, T_E), !, check(Env, app(E,tapp(X,int)), T), !,
    print_message(debug('a'),here_autre_sens(app(E,tapp(X,T_E)))).

%% 3
check(Env, if(E,E1,E2), T) :-
    % print_message(debug('check'), checking(if(E,E1,E2))),
    check_type(T_E, bool), check_type(T_E1, T), check_type(T_E2, T),
    check(Env, E, T_E), check(Env, E1, T_E1), check(Env, E2, T_E2), !.

%% 4
check(Env, fn(X,E), type -> T_E) :-
    % print_message(debug('check'), checking(fn(X,E))),
    % check_type(T_X, T1), check_type(T_E, T2),     %% utile?
    % check(Env, X, T_X), check(Env, E, T_E), !. %% ajout de X dans env? 
    NewEnv = [(X,type,val)|Env], check(NewEnv, E, T_E), !. %% ajout de X dans env? 
    % append((X,T_X,val),Env, NewEnv), check(NewEnv, E, T_E), !. %% ajout de X dans env? 

    %%lookup(Env,X,T,V) , ! -> 

%% 5
% check(Env, app(tapp(E1,_),E2), T) :-
%     check(Env, E2, T_E2),
%     % print_message(debug('check'),app_tapp(Env)),
%     lookup(Env, E1, forall(A,T2), _), !,
%     % lookup(Env, E1, X, _), !,
%     subst(T2,A,T_E2,T), !.

check(Env, app(E1,E2), T2) :-
    check(Env, E2, T1), !, check(Env, E1, T1 -> T2), !,
    print_message(debug('check'), checling(app(E1,E2))).

%% 6
check(Env, tfn(A,E), forall(?,T)) :-
    % check(Env, A, T_A), !, check_type(T_A, type), check(Env, E, T), !. %% ajout de A dans Env????
    % print_message(debug('check'),env(Env)),
    % print_message(debug('check'),newEnv(NewEnv)),
    NewEnv = [(A,type,type)|Env], check(NewEnv, E, T), !.

%% 7
check(Env, tapp(E,T1), T) :-
    % check(Env, E, forall(A,T2)), !, lookup(Env, E, T1, V), !, check(Env, T1, type), %% ????????
    % print_message(debug('a'),tapp_message(E,T1,V)),subst(T2,T1,A,T), !.
    print_message(debug('a'),checking_tapp(Env)),
    lookup(Env, E, forall(A,T2), _), !, subst(T2,A,T1,T), !,
    print_message(debug('tapp'),check_tapp(E,T1,T)).
%%pb : comment savoir quel type est inféré?

%% 8
check(_, quote(_), sexp).

%% 9
check(Env, list(T), type) :- check(Env, T, type), !.

%% 10
check(Env, T1 -> T2, type) :- check(Env, T1, type), check(Env, T2, type), !.

%% 11
check(Env, forall(A,T), type) :-
    NewEnv = [(A,type,type)|Env], check(NewEnv, T, type), !. %% ajout de A dans Env ????

check(_,_,_).
check(_,E,_) :- %%print_message(debug('check'),check_vide), !. %% En attendant, accepter n'importe quoi!
    print_message(error, check_error(E)), fail.



%% elaborate(+Env, +Exp, -NewExp)
%% Renvoie la version expansée de Exp, ce qui inclus:
%% - expansion de macros.
%% - expansion du sucre syntaxique fun(arg1, arg2, ...).
%% - ajout des instantiations de types.                         %% instancie la fonction polymorphe au type adapté ([T/a])

elaborate(_, Exp, Exp) :- number(Exp).

%% list
elaborate(Env, list(T), list(T_)) :-
    elaborate(Env, T, T_), !. %??????

%% forall
elaborate(_, forall(E), forall(E)). %%?? E a evaluer ou pas?

%% define
elaborate(Env, define(X,E), define(X_exp,E_exp)) :-
    elaborate(Env, X, X_exp), elaborate(Env, E, E_exp), !.

%% définition de type
% elaborate(Env, X : T, X : T_) :- elaborate(Env, T, T_).
elaborate(Env, X : T, X : T).

%% app
elaborate(Env, app(E1,E2), app(E1_,E2_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.

%% fn
elaborate(Env, fn(E1,E2), fn(E1,E2)).
% elaborate(Env, fn(E1,E2), tfn(E1_,fn(E1_,E2_))) :-
%     elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.


%% quote
elaborate(Env, quote(E), quote(E_)) :- elaborate(Env, E, E_), !.

%% if
elaborate(Env, if(E1,E2,E3), if(E1_,E2_, E3_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), elaborate(Env, E3, E3_), !.

%% tfn
elaborate(Env, tfn(E1,E2), tfn(E1_,E2_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.

%% tapp
elaborate(Env, tapp(E1,E2), tapp(E1_,E2_)) :-
    elaborate(Env, E1, E1_), elaborate(Env, E2, E2_), !.


elaborate(Env, Exp, NewExp) :-
    atom(Exp), lookup(Env, Exp, forall(_,_), _), ! ->
        NewExp = tapp(Exp,?).

elaborate(Env, Exp, Exp) :- atom(Exp).

% elaborate(Env, Exp, NewExp) :-
%     Exp =.. [Head|Args], Args = [E1|ES],
%     (lookup(Env, Head, T, builtin(macro)) ->
%         print_message(debug('a'),macro_trouve(T)),
%         elim_suc(Env, app(Head, E1), ES, NewExp)), !.

%% fonction type polymorphe
elaborate(Env, Exp, NewExp) :-
    Exp =.. [Head|Args], Args = [E1|ES],
    (lookup(Env, Head, forall(_,_), _), !, elaborate(Env, E1, E1_) ->
        % print_message(debug('sss'), branch1(Exp, Head, Args)), 
        elim_suc(Env, app(tapp(Head,?), E1_), ES, NewExp);
        % print_message(debug('sss'), branch2(Exp, Head, Args)),
        elim_suc(Env, app(Head, E1_), ES, NewExp)), !.


elaborate(Env, Exp, NewExp) :-
    Exp =.. [Head|Args], Args = [E1|ES],
    lookup(Env, Head, _, _) ->
        elim_suc(Env, app(Head, E1), ES, NewExp), !.


elim_suc(_, Exp, [], Exp). %% :- print_message(debug(''),fin_elim(Exp)), !.
elim_suc(Env, Exp, [E|ES], NewExp) :-
    print_message(debug('dd'),elim_suc(E)),
    (elaborate(Env, E, NewE) ->
        (lookup(Env, NewE, _, _) ->
            elim_suc(Env, app(Exp, tapp(NewE,?)), ES, NewExp), !;
            elim_suc(Env, app(Exp, NewE), ES, NewExp) ,!);
        (lookup(Env, E, _, _) ->
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
        [define(zero, 0),
         define(zero_0, app(app(+, zero), zero)),
         define(id_int, fn(i, app(app(+, i), zero))),
         define(zero_1, app(id_int, zero)),
         identity : forall(t, (t -> t)),
         define(identity, tfn(t, fn(x,x))),
         define(zero_2, identity(zero)),
         %% Pour pouvoir écrire "mklist(1,2,3)".
         define(mklist,
                macro(fn(args,
                         makenode(quote(cons),
                                  cons(car(args),
                                       cons(if(empty(cdr(args)),
                                               quote(nil),
                                               makenode(quote(mklist),
                                                        cdr(args))),
                                            nil))))))
        %  %% Pas aussi pratique que quasiquote/unquote, mais quand même
        %  %% un peu mieux que just "makenode".
        %  define(makeqnode,
        %         macro(fn(args,
        %                  makenode(quote(makenode),
        %                           mklist(makenode(quote(quote),
        %                                           mklist(car(args))),
        %                                  makenode(quote(mklist),
        %                                           cdr(args))))))),
        %  %% Pour pouvoir définir ses macros avec "defmacro(name,args,e)".
        %  define(defmacro,
        %         macro(fn(args,
        %                  makeqnode(define,
        %                            car(args),
        %                            makeqnode(macro,
        %                                      makenode(quote(fn),
        %                                               cdr(args))))))),
        %  %% Pour pouvoir définir ses variables avec "X = E" plutôt qu'avec
        %  %% "define".
        %  defmacro(=, args, makenode(quote(define),args)),
        %  %% Les déclarations offrent un sorte de "let" récursif global,
        %  %% et cette macro-ci offre un "let(x,e1,e2)" pour ajouter une
        %  %% déclaration locale.
        %  defmacro(let, args,
        %           makeqnode(app,
        %                     makeqnode(fn, car(args), car(cdr(cdr(args)))),
        %                     car(cdr(args)))),
        %  %% Notre bonne vieille fonction "map", qui a besoin d'une
        %  %% déclaration de type, vu qu'elle est récursive.
        %  map : forall(a, forall(b, ((a -> b) -> list(a) -> list(b)))),
        %  map = tfn(a, tfn(b, fn(f, fn(xs,
        %                               if(empty(xs),
        %                                  nil,
        %                                  cons(f(car(xs)), map(f,cdr(xs))))))))
    ]).

%% runraw(+Prog, -Val)
%% Exécute programme Prog dans l'environnement initial.
runraw(P, V) :- env0(Env), eval_decls(Env, P, V).

%% run(+Prog, -Val)
%% Comme `runraw`, mais ajoute l'environnement "pervasive" défini ci-dessus.
run(P, V) :- env0(Env), pervasive(Per), append(Per, P, Code),
             eval_decls(Env, Code, V).
