%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Prolog Effect System    
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_flag(toplevel_print_options, [max_depth(50)]).
:- use_module(library(ordsets)).

:- op(1180, fx, handle).
:- op(1170, yfx, with).
:- op(1160, yfx, finally).
:- op(1150, yfx, for).


:- dynamic context/2.
:- dynamic predicate_context/2.
:- dynamic h_in_p/4.
:- dynamic prog_pred/2.



%********************************************************************
% infer_effects/2
% Main predicate to be called to infer a goal.
%
%
infer_effects(G,E,Eopt):- top_infer(empty,G,E), optimize(E,Eopt),!.

%********************************************************************
% optimize/2
% optimizer predicate to replace effects syntax into all_of/1 and 
% none_of/1.
%
%

optimize(empty,all_of([])):- !.
optimize(any, none_of([])):- !.
optimize(op(Op),all_of([Op])):- !.
optimize(all_of(X),all_of(X)):- !.
optimize(none_of(X),none_of(X)):- !.

optimize(union(all_of(L),B),E):- !,optimize(B,B1), unionify(all_of(L),B1,E).
optimize(union(B,all_of(L)),E):- !,optimize(B,B1), unionify(all_of(L),B1,E).
optimize(union(none_of(L),B),E):-!,optimize(B,B1), unionify(none_of(L),B1,E).
optimize(union(B,none_of(L)),E):-!, optimize(B,B1), unionify(none_of(L),B1,E).
optimize(union(A,B),E):- !,optimize(A,A1), optimize(B,B1), unionify(A1,B1,E).

optimize(minus(A,B),E):- !,optimize(A,A1), optimize(B,B1), differencify(A1,B1,E).

unionify(Y,X,Y):- var(X),!.
unionify(X,Y,Y):- var(X),!.
unionify(all_of(L1),X,all_of(L1)):- var(X),!.
unionify(all_of(L1),all_of(L2),all_of(L)):- ord_union(L1,L2,L),!. 
unionify(none_of(L1),none_of(L2),none_of(L)):- ord_intersection(L1,L2,L),!.
unionify(all_of(L1),none_of(L2),none_of(L)):- ord_subtract(L2,L1,L),!.
unionify(none_of(L2),all_of(L1),none_of(L)):- ord_subtract(L2,L1,L),!.

differencify(all_of(L1),all_of(L2),all_of(L)):- ord_subtract(L1,L2,L).
differencify(none_of(L1),none_of(L2),none_of(L)):- ord_union(L1,L2,L).
differencify(all_of(L1),none_of(L2),all_of(L)):- ord_intersection(L1,L2,L).
differencify(none_of(L1),all_of(L2),none_of(L)):- ord_union(L1,L2,L).



equal_opt_context(all_of(L),all_of(L)).
equal_opt_context(none_of(L),none_of(L)).

%*******************************************************************
% context_contain(a,B)
% Checks if the context B is contained in the context a
%	
%
%
%
context_contain(any,any).
context_contain(empty,empty).
context_contain(container(C),container(C)).
context_contain(union(A,B),C):- context_contain(A,C) ;
								context_contain(B,C) .

context_contain(minus(A,B),C):- context_contain(A,C) ;
								context_contain(B,C) .
context_contain(all_of(_),_):- fail.
context_contain(none_of(_),_):- fail.
context_contain(X,Y) :- X=Y.


%********************************************************************
% context_replace/4
% Replaces a context container (whether continuation or predicate context)
% with a replacement clause
%
%
context_replace(container(C),container(C),Replace,Replace).
context_replace(container(C),container(Z),_,container(C)):- C \= Z.
context_replace(union(A,B),C,Replace,union(X,Y)):-
							context_replace(A,C,Replace,X),
							context_replace(B,C,Replace,Y).

context_replace(minus(A,B),C,Replace,minus(X,Y)):-
							context_replace(A,C,Replace,X),
							context_replace(B,C,Replace,Y).

context_replace(X,_,_,X).

%********************************************************************


%********************************************************************
% varianle_replace/4
% Replaces any variable in the context to the replaced value
%
%

variable_replace(EC,V,Replace,Replace):- var(EC).

variable_replace(union(A,B),V,Replace,union(X,Y)):-
							variable_replace(A,V,Replace,X),
							variable_replace(B,V,Replace,Y).

variable_replace(minus(A,B),V,Replace,minus(X,Y)):-
							variable_replace(A,V,Replace,X),
							variable_replace(B,V,Replace,Y).

variable_replace(EC,_,_,EC):- \+var(EC).


%********************************************************************
%infer/5
% EC : main context.
% C  : Continuation context.
% C1 : user defined predicate contexts.
% G  : Goal
% E  : Result effects
% C and C1 are used by lfp to calculate the least fix points

top_infer(EC,G,E):- infer(EC,_,_,G,E),
					retractall(predicate_context(_,_)).



infer(_,_,_,G,any):- var(G),!.

infer(EC,C,C1,G,E):-  
	G = (G1,G2),
	infer(EC,C,C1,G1,E1), 
	infer(EC,C,C1,G2,E2),
	E = union(E1,E2),!.

infer(EC,C,C1,G,E):- 
	G = (G1;G2),
	infer(EC,C,C1,G1,E1),
	infer(EC,C,C1,G2,E2), 
	E = union(E1,E2),!.


infer(_,C,_,G,container(C)):- G=..[continue|_],!. 

infer(_,_,_,G,op(Functor)):- 
	G=..[Functor|T], 
	length(T,N),
	effect_list(EffectList),
    member(Functor/N,EffectList),!.


infer(_,_,_,G,empty):- predicate_property(G,built_in),!.

infer(EC,_,C1,(handle G0 with Switches finally Gf for _), E):- infer_handler(EC,C1,G0,Switches,Gf,E).
infer(EC,_,C1,(handle G0 with Switches finally Gf), E) :- infer_handler(EC,C1,G0,Switches,Gf,E).
infer(EC,_,C1,(handle G0 with Switches for _), E) :- infer_handler(EC,C1,G0,Switches,true,E).
infer(EC,_,C1,(handle G0 with Switches), E) :- infer_handler(EC,C1,G0,Switches,true,E).

infer(_,_,C1,G,E):- 
	prog_pred(G,_),
	G=..[Functor|L1],
	length(L1,N),
	predicate_context(Functor/N,C1),
	E = container(C1),!.


infer(EC,C,_,G,E):-
	findall(GG,prog_pred(G,GG),Clauses),
	G=..[Functor|L1],
	length(L1,N),
	gensym(context,C1),
	assert(predicate_context(Functor/N,C1)),
	infer_all(EC,C,C1,Clauses,empty,Egeneral),
	(
	  h_in_p(EGH,CH,EH,C1) ->
	    retract(h_in_p(_,_,_,C1)),
	    variable_replace(Egeneral,EH,EGH,EGPGeneral), 
	    lfp2(EGH,EGPGeneral,CH,C1,empty,empty,EH,E)
	;
	  context_has_context(Egeneral,C1) ->
	  	lfp(Egeneral,C1,empty,E)
	;
	    E = Egeneral
	).


%******************************************
% infer_handler/ 6
% infers the effects that can be thrown by a handler. A handled effect is
% not included in the result, because if it is called, it will be handled right away.
% In other words, it infers the effects of G0 (that are not handled by the handler) plus
% all the effects in the switches goals and the finally goal GF.
% 
% EC is the main context
% C1 is the user defined predicate context (in case the handler is inside a goal of a predicate)
% G0 is the handler's goal
% Switches is the handler switches/ operations
% GF is the finally goal 
% E is the resulting infered effects

infer_handler(EC,C1,G0,Switches,GF,E) :- 
	% write('G0 = ') ,write(G0), nl,
	% write('SW = '), write(Switches),nl,
	% write('GF = '), write(GF), nl,
	get_ops_goals(Switches,OpsList,GoalsList),
	get_ops_effects(OpsList,OpsEffectList),
	% generating handler context 
	gensym(context,C),
	assert(context(C,E)),
	infer_switches(E,C,GoalsList,ESwitches),
	infer(EC,C,_,G0,E0),
	infer(EC,C,_,GF,Ef),
	list_to_ord_set(OpsEffectList, OpsSet),
	% write('opset :- '), write(OpsSet), nl,
	E0MinusOps = minus(E0,all_of(OpsSet)),
	E0MinusOpsUEf = union(E0MinusOps,Ef),
	Egeneral = union(E0MinusOpsUEf,ESwitches),
	(
		context_has_context(Egeneral,C) ->
		 ( (\+var(C1) , context_has_context(Egeneral,C1) ) ->
			  assert(h_in_p(Egeneral,C,E,C1))
		 	 ;
		     lfp(Egeneral,C,empty,E)
	)
	;
		E = Egeneral
	).




infer_all(_,_,_,[],E,E).
infer_all(EC,C,C1,[H|T],Acc,Egeneral):- infer(EC,C,C1,H,E),
								   Acc1 = union(Acc,E),
								   infer_all(EC,C,C1,T,Acc1,Egeneral).




context_has_context(E,C):- context_contain(E,container(C)).



lfp2(EGH,EGP,CH,CP,ReplaceH,ReplaceP,EH,EP):- 
	context_replace(EGH,container(CP),ReplaceP,EH1),
	lfp(EH1,CH,ReplaceH,EH1lfp),
	context_replace(EGP,container(CH),EH1lfp,EPOnly),
	context_replace(EPOnly,container(CP),ReplaceP,EPOnly1),
	context_replace(EPOnly,container(CP),EPOnly1,EPOnly2),
	optimize(EPOnly1,EPOnly1Opt),
	optimize(EPOnly2,EPOnly2Opt),
	equal_opt_context(EPOnly1Opt,EPOnly2Opt)->
	(
		EP = EPOnly1 , EH = EH1lfp
		;
		lfp2(EGH,EGP,CH,CP,ReplaceH,EPOnly1,EH,EP)
	).



lfp(EG,C,Replace,E):- 
	context_replace(EG,container(C),Replace,EG1),
	context_replace(EG,container(C),EG1,EG2),
	optimize(EG1,EG1Opt),
	optimize(EG2,EG2Opt),
	equal_opt_context(EG1Opt,EG2Opt)->
	(
		E = EG1
		;
		lfp(EG,C,EG1,E)
	).






get_ops_goals((A->B),[A],[B]).
get_ops_goals(( (A->B) ; C),[A|T1],[B|T2]):- get_ops_goals(C,T1,T2).

get_ops_effects([],[]).
get_ops_effects([A|T],[B|T2]):- 
	A =..[B|_], 
	get_ops_effects(T,T2).


infer_switches(_,_,[],empty).
infer_switches(E,C,[H|T],EU):- 
	 infer(E,C,_,H,EH),
	 infer_switches(E,C,T,ET),
	 EU = union(EH,ET).   





%%% reset_gensym(+Prefix)
%%% ---------------------
:- dynamic gensym_counter/2.
reset_gensym(all) :- !, retractall(gensym_counter(_,_)).
reset_gensym(Prefix) :- retractall(gensym_counter(Prefix,_)).


%%% gensym(+Prefix,-NewSymbol)
%%% --------------------------

gensym(Prefix,NewSymbol) :-
        retract(gensym_counter(Prefix,Old)),
        New is Old + 1,
        assert(gensym_counter(Prefix,New)),
        concat(Prefix,New,NewSymbol), !.

gensym(Prefix,NewSymbol) :-
        assert(gensym_counter(Prefix,0)),
        concat(Prefix,0,NewSymbol).

concat(S1,S2,S3) :-
        name(S1,L1),
        name(S2,L2),
        append(L1,L2,L3),
        name(S3,L3).
