%Author:- Amr Hany Saleh
%Date :- 01/05/2016

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Effect Handler Compiler     
%
%  -Compiles special effect handler syntax.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:-consult('EffectSystem').

:- op(1180, fx, handle).
:- op(1170, yfx, with).
:- op(1160, yfx, finally).
:- op(1150, yfx, for).

:- dynamic effect/1, handler/5, contains_handler/3,
		   pred_region/2, pred_handles/2, subsume_handler/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	compile_effects(+file, +optimizationFlag, +file)
%	
%	Main predicate in the compiler, takes a padp file and
%	compiles it in chrism file.
%

compile_effects(File,Optimize,OutFile) :-
        open(OutFile,write,OutStream),
        assert(output_stream(OutStream)),
        parse_file(File,Optimize),
        close(OutStream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	fatal_error(+clause)
%
%	put for debugging reasons to check for fatal errors.
%
fatal_error(X) :- 
        told,
        tell('effect_fatal_error'),
        write(X),
        told,
        halt(1).        % exit codes do not seem to work


syntax_error :- told, halt.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	Writeclause(+clause)
%
%	writes a given clause into the chrism file
%

writeclause(C) :-
    output_stream(OutStream),
    portray_clause(OutStream,C).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	parse_file(+file)
%
%	starts parsing the padp file
%
parse_file(File,Optimize) :-
        open(File,read,Stream),
        parse_rules(Stream,1),
   		after_parse(Optimize),
        close(Stream).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	parse_rules(+Stream, +counter)
%
%	starts parsing every rule in the given padp file
%
parse_rules(Stream,Counter) :-
    tell('syntax_error'),
    catch(read_term(Stream,Term,[]),_,syntax_error),
    told, 
    ( Term = end_of_file -> 
    	write('\nend of input file')
    ; parse_rule(Term,Counter,Counter1) ->
    	parse_rules(Stream,Counter1)
    ; fatal_error('This should not happen')
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	parse_rule(+term, +counter, ?counter1)
%
%	starts parsing a given rule according its term type.
%

parse_rule((:- effect_list(M)) , N , N) :- 
	assert(effect_list(M)).

parse_rule((Head:- Body) , N , N) :- 
	assert(prog_pred(Head,Body)).

parse_rule((handle _),N,N) :- 
	fatal_error('handler not in a predicate').

parse_rule(Term,N,N) :- 
	assert(prog_pred(Term,true)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	after_parse
%
%	after parsing the rules, start to check handlers and merging.
%

after_parse(Optimize):- 
	(Optimize -> optimize_program ; true),
	findall((Head,Body),prog_pred(Head,Body),List),
	replace_handlers(List),
	compile_handlers,
	write_all_clauses.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	OPTIMIZATION MODULE
%
%	THIS IS THE PART WHERE THE PROGRAM GETS OPTIMIZED WITH THE
%	OPTIMIZATION RULES IN THE PAPER
%
optimize_program:- 
	findall((Head,Body),prog_pred(Head,Body),List),
	optimize_preds(List).

optimize_preds([]).
optimize_preds([(Head,Body)|T]):-
	optimize_predicate(Head,Body,NewHead,NewBody),
	partial_evaluate(NewBody,NewerBody),
	resolve_equality(NewHead,NewerBody,UltimateBody),
	retract(prog_pred(Head,Body)),
	assert(prog_pred(NewHead,UltimateBody)),
	optimize_preds(T).


optimize_predicate(Head,Body,NewHead,NewerBody):-
	body_contains_handlers(Body,Handlers),
	optimize_handlers(Head,Handlers,OptClauses),
	replace_handlers_by_optimized_clauses(Body,Handlers,OptClauses,NewBody),
	check_handler_merging(NewBody,TobeMerged),
	merge_handlers(TobeMerged,MergedHandlers),
	replace_handlers_by_optimized_clauses(NewBody,TobeMerged,MergedHandlers,NewerBody),
	Head = NewHead.


replace_handlers_by_optimized_clauses(Body,[],[],Body).
replace_handlers_by_optimized_clauses(Body,[Handler|T],[OptClause|T2],NewBody):-
				replace_handler_by_query(Body,Handler,OptClause,TempBody),
				replace_handlers_by_optimized_clauses(TempBody,T,T2,NewBody).

optimize_handlers(_,[],[]).
optimize_handlers(Head,[Handler|T],[OptClause|T2]):-
	get_handler_data(Handler,G,Sw,Fin,For),
	body_contains_handlers(G,Handlers),
	length(Handlers,N), 
	(N >0 -> 		
		optimize_handlers(_,Handlers,OptClauses),
		replace_handlers_by_optimized_clauses(G,Handlers,OptClauses,NewBody)
	;
		NewBody = G
	),
	optimize_handler(Head,NewBody,Sw,Fin,For,OptClause1),
	resolve_equality(_,OptClause1,OptClause),
	optimize_handlers(Head,T,T2).


get_handler_data((handle G with Sw finally Fin for For), G,Sw,Fin,For).
get_handler_data((handle G with Sw  for For), G,Sw,true,For).
get_handler_data((handle G with Sw finally Fin), G,Sw,Fin,true).
get_handler_data((handle G with Sw ), G,Sw,true,true).


optimize_handler(_,G,Sw,Fin,For,(handle G with Sw finally Fin for For)):- var(G),!.

optimize_handler(_,G,Sw,Fin,For,(handle G with Sw finally Fin for For)):- G = (handle _), !.

optimize_handler(Head,(G1,G2),Sw,Fin,For,(G1,OptClause)) :-
	infer_effects(G1,_,Eopt),
	Eopt = all_of(L),
	get_switch_ops(Sw,Lops),
	list_to_ord_set(Lops,LopsSet),
	ord_intersection(L,LopsSet,[]),
	optimize_handler(Head,G2,Sw,Fin,For,OptClause),!.


optimize_handler(Head,(G1;G2),Sw,Fin,For,OptClause) :-
	optimize_handler(Head,G1,Sw,Fin,For,OptC1),
	get_args_list(For,_,AArgs),
	refresh_handler(G2,Sw,Fin,For,AArgs,NewHandler),
	NewHandler = (handle G2 with NewSwitches finally NewGF for NewHandlerFor),
	optimize_handler(Head,G2,NewSwitches,NewGF,NewHandlerFor,OptC2),
	OptClause = (OptC1 ; OptC2),!.


optimize_handler(_,G,Sw,Fin,For,OptClause) :-
	infer_effects(G,_,Eopt),
	Eopt = all_of(L),
	get_switch_ops(Sw,Lops),
	list_to_ord_set(Lops,LopsSet),
	ord_intersection(L,LopsSet,[]),
	OptClause = (G,For,Fin),!.




optimize_handler(Head,G1,Sw,Fin,For,OptClause) :-
	functor(G1,Gn,_),
	get_switch_ops(Sw,Lops),
	member(Gn,Lops),
	in_switches(Sw,G1,FormalOp,Body),
	Cont= true,
	make_cont_goal(Cont,Sw,Fin,For,Body,New_Goal),
	optimize_predicate(Head,((G1 = FormalOp),New_Goal),_,OptClause),!.
	


optimize_handler(Head,(G1,G2),Sw,Fin,For,OptClause) :-
	functor(G1,Gn,_),
	get_switch_ops(Sw,Lops),
	member(Gn,Lops),
	in_switches(Sw,G1,FormalOp,Body),
	Cont= G2,
	make_cont_goal(Cont,Sw,Fin,For,Body,New_Goal),
	optimize_predicate(Head,((G1 = FormalOp),New_Goal),_,OptClause),!.




optimize_handler(_,G,Sw,Fin,For,(handle G with Sw finally Fin for For)).





get_switch_ops(((Op->_);Rest),[OpFunctor|T]):- functor(Op,OpFunctor,_), get_switch_ops(Rest,T).
get_switch_ops((Op->_),[OpFunctor]):- functor(Op,OpFunctor,_).


in_switches((A->B),Op,A,B)       :- functor(Op,OpN,OpA), 
									functor(A,OpN,OpA). 

in_switches(((A->B) ; _),Op,A,B) :- functor(Op,OpN,OpA), 
									functor(A,OpN,OpA), !.

in_switches(((_->_) ; C),Op,A,B) :- in_switches(C,Op,A,B).


make_cont_goal(Cont,Switches,Gf,Args,(G1,G2),(G1R,G2R)):- !,
	make_cont_goal(Cont,Switches,Gf,Args,G1,G1R),
	make_cont_goal(Cont,Switches,Gf,Args,G2,G2R).	



make_cont_goal(Cont,Switches,Gf,Args,(G1;G2),(G1R;G2R)):- !,
	make_cont_goal(Cont,Switches,Gf,Args,G1,G1R),
	make_cont_goal(Cont,Switches,Gf,Args,G2,G2R).	


make_cont_goal(Cont,Switches,Gf,Args,((C -> G1;G2)),Result):- 
	!,
	make_cont_goal(Cont,Switches,Gf,Args,C,CR),
	make_cont_goal(Cont,Switches,Gf,Args,G1,G1R),
	make_cont_goal(Cont,Switches,Gf,Args,G2,G2R),
	Result = (CR -> G1R ; G2R).	


make_cont_goal(Cont,Switches,Gf,Args,G1,(Args,NewHandler)):- 
	G1=..[continue|ContArgs], !,
	refresh_handler(Cont,Switches,Gf,Args,ContArgs,NewHandler).


make_cont_goal(_,_,_,_,G,G):- !.



refresh_handler(Cont,Switches,Gf,Args,ContArgs,NewHandler):-
	copy_term( (Switches+Gf+Args) , (NewSwitches+NewGF+NewArgs) ),
	make_new_for_args(NewArgs,ContArgs,NewHandlerFor),
	NewHandler = (handle Cont with NewSwitches finally NewGF for NewHandlerFor).



make_new_for_args(true,[],true).

make_new_for_args((X_new=Y_new),[ContArgOld],(X_new = ContArgOld)). 

make_new_for_args(((X_new=Y_new),NewArgs),[ContArgOld|ContArgsOld],( X_new = ContArgOld, T)) :-
	make_new_for_args(NewArgs,ContArgsOld,T).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	Resolving Equality Module
%
%

resolve_equality(_,Body,Result):-
	make_equal(Body,Result1),
	remove_dummy_true(Result1,Result).

make_equal(G,G):- var(G),!.

make_equal(G1,true):-
	G1 = (A = B),!,
	A = B.

make_equal((G1,G2),(G1R,G2R)):- !,
	make_equal(G1,G1R),
	make_equal(G2,G2R).

make_equal(G,G).


remove_dummy_true(G,G1):- 
	conj_to_list(G,GList),!,
	delete_true(GList,G1List),
	list_to_conj(G1List,G1).




delete_true([],[]).

delete_true([G|T],[G|T2]):-
	var(G),!,
	delete_true(T,T2).

delete_true([G|T],T2):-
	G== true,!,
	delete_true(T,T2).

delete_true([G|T],R):-
	 G = (G1,G2),
	 remove_dummy_true(G1,G1R),
	 conj_to_list(G1R,G1RL),
	 remove_dummy_true(G2,G2R),
	 conj_to_list(G2R,G2RL),
	 append(G1RL,G2RL,GRL),
	 delete_true(GRL,GRLL),
	 delete_true(T,T2),
	 append(GRLL,T2,R).

delete_true([G|T],[G|T2]):-
	 \+(G==true),!,
	 delete_true(T,T2).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	Partial Evaluation Module
%
%	for now super simple, will get compilicated !
%
%




partial_evaluate(G,G):- var(G),!.

partial_evaluate((G1,G2),(G1R,G2R)):-!,
	partial_evaluate(G1,G1R),
	partial_evaluate(G2,G2R).

partial_evaluate((C->G1;G2) , (CR->G1R;G2R)):-!,
	partial_evaluate(C,CR),
	partial_evaluate(G1,G1R),
	partial_evaluate(G2,G2R).

partial_evaluate((G1;G2),(G1R;G2R)):-!,
	partial_evaluate(G1,G1R),
	partial_evaluate(G2,G2R).

partial_evaluate((handle G with R), (handle G with R)):-
	var(G),!.

partial_evaluate((handle G with R), GR):-!,
	\+var(G),
	findall((G,T),prog_pred(G,T),List),
	get_handler_data((handle G with R),_,Sw,Gf,For),
	G=..[PredName|PredArgs],
	gensym(PredName,NewPredName),
	partial_evaluate_pred(List,NewPredName,Sw,Gf,For),
	get_actual_args(For,ForAA),
	append(PredArgs,ForAA,MainArgs),
	GR =..[NewPredName|MainArgs],!.


partial_evaluate(G1,Result):-
	findall(T,prog_pred(G1,T),List),
	length(List,1),!,
	prog_pred(G1,R),
	partial_evaluate(R,Result).

partial_evaluate(G,G):- !.

partial_evaluate_pred([],_,_,_,_).
partial_evaluate_pred([(Head,Body)|T],NewPredName,Sw,Gf,For):-
	infer_effects(Body,_,Eopt),
	Eopt == all_of([]),!,
	get_actual_args(For,ForAA),
	Head =.. [_|PredArgs],
	append(PredArgs,ForAA,MainArgs),
	NewHead =..[NewPredName|MainArgs],
	NewBody = (Body,Gf,For),
	copy_term(NewHead+NewBody,NewHead1+NewBody1),
	resolve_equality(NewHead1,NewBody1,NewerBody),
	assert(prog_pred(NewHead1,NewerBody)),
	partial_evaluate_pred(T,NewPredName,Sw,Gf,For).


partial_evaluate_pred([(Head,Body)|T],NewPredName,Sw,Gf,For):-
	get_actual_args(For,ForAA),
	Head =.. [_|PredArgs],
	append(PredArgs,ForAA,MainArgs),
	NewHead =..[NewPredName|MainArgs],
	optimize_handler(_,Body,Sw,Gf,For,OptClause),
	body_contains_handlers(OptClause,Handlers),
	get_handler_opt_clause(Head,NewPredName,Handlers,Opt_Clauses),
	replace_handlers_by_optimized_clauses(OptClause,Handlers,Opt_Clauses,NewBody),
	copy_term(NewHead+NewBody,NewHead1+NewBody1),
	resolve_equality(NewHead1,NewBody1,NewerBody),
	assert(prog_pred(NewHead1,NewerBody)),
	partial_evaluate_pred(T,NewPredName,Sw,Gf,For).



get_handler_opt_clause(_,_,[],[]).
get_handler_opt_clause(Head,NewPredName,[Handler|T],[OptClause|T2]):-
	get_handler_data(Handler,G,_,_,For),
	functor(G,Fname,Fari),
	functor(Head,Fname,Fari),
	get_actual_args(For,ForAA),
	G=..[Fname|PredArgs],
	append(PredArgs,ForAA,MainArgs),
	OptClause=..[NewPredName|MainArgs],
	get_handler_opt_clause(Head,NewPredName,T,T2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	Handlers merging Module
%
%	used to merge the handlers when they are still in the 
%	handle..with syntax.
%
%

check_handler_merging(G,[]):- var(G),!.

check_handler_merging((G1,G2),List):-!,
	check_handler_merging(G1,L1),
	check_handler_merging(G2,L2),
	append(L1,L2,List).

check_handler_merging((G1;G2),List):-!,
	check_handler_merging(G1,L1),
	check_handler_merging(G2,L2),
	append(L1,L2,List).

check_handler_merging(G, [G]) :-
	G = (handle X with _),
	\+ var(X),
	X = (handle _),!.

check_handler_merging(_,[]):- !.





merge_handlers([],[]).

merge_handlers([Composite|T],[Merged|T2]):-
	Composite = (handle Inner with _),
	Inner = (handle _ with _),
	get_handler_data(Composite,G,SwOut,Gfout,Forout),
	get_handler_data(Inner,Gin,Swin,Gfin,Forin),
	G == Inner,
	get_switch_ops(SwOut,Sw1ops),
	get_switch_ops(Swin,Sw2ops),
	list_to_ord_set(Sw1ops,Sw1opsSet),
	list_to_ord_set(Sw2ops,Sw2opsSet),
	ord_disjoint(Sw1opsSet, Sw2opsSet),
	inner_not_call_outer(Swin,Sw1ops),
	inner_not_call_outer(Gfin,Sw1ops),
	no_continue_in_goal(Gfin),
	make_merged_handler(Gin,Swin,Gfin,Forin,SwOut,Gfout,Forout,Merged),
	merge_handlers(T,T2),!.



merge_handlers([Composite|T],[ResultingHandler|T2]):-
	Composite = (handle Inner with _),
	Inner = (handle _ with _),
	get_handler_data(Composite,G,SwOut,Gfout,Forout),
	get_handler_data(Inner,Gin,Swin,Gfin,Forin),
	G == Inner,
	switches_end_with_continue(Swin),
	combine_fors(Forout,Forin,MainFor),
	get_formal_args(Forout,ForOutFArgs),
	modify_switches(Swin,0,ForOutFArgs,MainSwitches),
	get_formal_args(Forin,ForinFArgs),
	length(ForinFArgs,Length),
	length(FreshForinFargs,Length),
	modify_switches(SwOut,1,FreshForinFargs,NewSwout),
	make_for_reverse(FreshForinFargs,ForinFArgs,Forout,NewForOut),
	make_handler_wrapping(NewSwout,Gfout,NewForOut,MainSwitches,MainFor,NewSwitches),
	disj_to_list(NewSwitches,NewSwitchesList),
	disj_to_list(NewSwout,NewSwoutList),
	append(NewSwitchesList,NewSwoutList,TopMainSwitchesL),
	list_to_disj(TopMainSwitchesL,TopMainSwitches),
	make_finally_wrapping(NewSwout,Gfout,NewForOut,Gfin,MainFor,MainGf),
	ResultingHandler = (handle Gin with TopMainSwitches finally MainGf for MainFor),
	merge_handlers(T,T2).



merge_handlers([Composite|T],[Composite|T2]):-
	!,merge_handlers(T,T2).


make_handler_wrapping(NewSwout,Gfout,NewForOut,MainSwitches,MainFor,NewSwitches):-
	disj_to_list(MainSwitches,MainSwitchesList),
	wrap_every_switch(NewSwout,Gfout,NewForOut,MainSwitchesList,MainFor,NewSwitchesList),
	list_to_disj(NewSwitchesList,NewSwitches).

wrap_every_switch(_,_,_,[],_,[]).

wrap_every_switch(NewSwout,Gfout,NewForOut,[Switch|T],MainFor,[NewSwitch|T2]):-
	Switch = (A -> SwitchBody),
	goal_end_with_continue(SwitchBody,SwitchGoal,SwitchContinue),
	copy_term((NewSwout+SwitchContinue+NewForOut),(RefreshedSwout+RefreshedSwitchContinue+RefreshedForOut)),
	get_formal_args(MainFor,MainForFargs),
	change_for_a_args(RefreshedForOut,MainForFargs,WrappedHandlerFor),
	Handler = (handle SwitchGoal with RefreshedSwout finally RefreshedSwitchContinue for WrappedHandlerFor),
	optimize_predicate(_,Handler,_,OptHandler),
	NewSwitch = (A -> OptHandler),
	wrap_every_switch(NewSwout,Gfout,NewForOut,T,MainFor,T2).


make_finally_wrapping(NewSwout,Gfout,NewForOut,Gfin,MainFor,MainGf):-
	copy_term((NewSwout+Gfout+NewForOut),(RefreshedSwout+RefreshedGfout+RefreshedForOut)),
	get_formal_args(MainFor,MainForFargs),
	change_for_a_args(RefreshedForOut,MainForFargs,WrappedHandlerFor),
	Gf = (handle Gfin with RefreshedSwout finally RefreshedGfout for WrappedHandlerFor),
	optimize_predicate(_,Gf,_,MainGf).



change_for_a_args((A=_),[D],(A=D)).
change_for_a_args((A=_,Rest),[D|Tail],(A=D,Rest2)):-
	change_for_a_args(Rest,Tail,Rest2).


make_for([],[],Forin,Forin).
make_for([A|T],[B|T2],Forin,(A=B,Rest)):- make_for(T,T2,Forin,Rest).

make_for_reverse([],[],Forin,Forin).
make_for_reverse(L1,L2,Forin,Result):- 
	conj_to_list(Forin,ForinL),
	equate_list(L1,L2,Equality),
	conj_to_list(Equality,EqualityL),
	append(ForinL,EqualityL,MainL),
	list_to_conj(MainL,Result).

equate_list([H],[H2],(H=H2)):-!.
equate_list([H|T],[H2|T2],(H=H2,Rest)):- equate_list(T,T2,Rest).

switches_end_with_continue((_->B)):- 
	goal_end_with_continue(B,_,_).
switches_end_with_continue(((_->B);C)):- 
	goal_end_with_continue(B,_,_),
	switches_end_with_continue(C).


goal_end_with_continue(G,_,_):- var(G),!, fail.

goal_end_with_continue(G,true,G):- G=..[continue|_].

goal_end_with_continue((G1,_),_,_):- 
	\+var(G1), G1=..[continue|_], fail.

goal_end_with_continue((G1,_),_,_):- 
	\+ var(G1), fail.

goal_end_with_continue((G1,G2),(G1,Rest),Continue):- 
	goal_end_with_continue(G2,Rest,Continue).


inner_not_call_outer(G,_):- var(G),!,fail.

inner_not_call_outer((G1,G2),Ops):-
	inner_not_call_outer(G1,Ops),
	inner_not_call_outer(G2,Ops).

inner_not_call_outer((G1;G2),Ops):-
	inner_not_call_outer(G1,Ops),
	inner_not_call_outer(G2,Ops).

inner_not_call_outer(G,Ops):-
	functor(G,Gn,_),
	\+member(Gn,Ops). 



no_continue_in_goal(Gf):- var(Gf),!, fail.

no_continue_in_goal((Gf1,Gf2)):-!,
	no_continue_in_goal(Gf1),
	no_continue_in_goal(Gf2).

no_continue_in_goal((Gf1;Gf2)):-!,
	no_continue_in_goal(Gf1),
	no_continue_in_goal(Gf2).

no_continue_in_goal((C->(Gf1;Gf2))):-!,
	no_continue_in_goal(C),
	no_continue_in_goal(Gf1),
	no_continue_in_goal(Gf2).

no_continue_in_goal(G):- G =..[continue|_],!,fail.

no_continue_in_goal(_).



make_merged_handler(Gin,Swin,Gfin,Forin,Swout,Gfout,Forout,Merged):-
	get_formal_args(Forout,ForOutFargs),
	get_formal_args(Forin,ForinFargs),
	modify_switches(Swin,1,ForOutFargs,ModifiedSwin),
	modify_switches(Swout,0,ForinFargs,ModifiedSwOut),
	combine_switches(ModifiedSwin,ModifiedSwOut,MainSwitches),
	combine_fors(Forin,Forout,MainFor),
	Merged = (handle Gin with MainSwitches finally (Gfin,Gfout) for MainFor).




get_formal_args(G,[G]):- var(G).
get_formal_args(G,[]):- G ==true.
get_formal_args((F = _),[F]).
get_formal_args(((F = _),R),[F|T]):- get_formal_args(R,T).


get_actual_args(G,[G]):- var(G).
get_actual_args(G,[]):- G ==true.
get_actual_args((_ = F),[F]).
get_actual_args(((_ = F),R),[F|T]):- get_actual_args(R,T).



modify_switches((A->B),StartOrEnd,Args,(A->NewB)):-
	modify_switch(B,StartOrEnd,Args,NewB).

modify_switches(((A->B);Rest),StartOrEnd,Args,((A->NewB);NewRest)):-
	modify_switch(B,StartOrEnd,Args,NewB),
	modify_switches(Rest,StartOrEnd,Args,NewRest).


modify_switch(G,_,_,G):- 
	var(G),!.

modify_switch((G1,G2),StartOrEnd,Args,(G1New,G2New)):-!,
	modify_switch(G1,StartOrEnd,Args,G1New),
	modify_switch(G2,StartOrEnd,Args,G2New).


modify_switch((C-> (G1;G2)),StartOrEnd,Args,(C1 -> (G1New;G2New))):-!,
	modify_switch(C,StartOrEnd,Args,C1),
	modify_switch(G1,StartOrEnd,Args,G1New),
	modify_switch(G2,StartOrEnd,Args,G2New).

modify_switch((G1;G2),StartOrEnd,Args,(G1New;G2New)):-!,
	modify_switch(G1,StartOrEnd,Args,G1New),
	modify_switch(G2,StartOrEnd,Args,G2New).

modify_switch(G,0,Args,Result):-
	G=..[continue|T],!,
	append(Args,T,List),
	Result=..[continue|List].

modify_switch(G,1,Args,Result):-
	G=..[continue|T],!,
	append(T,Args,List),
	Result=..[continue|List].

modify_switch(G,_,_,G):- \+functor(G,continue,_).

combine_switches(Sw1,Sw2,MainSwitches):-
	disj_to_list(Sw1,Sw1L),
	disj_to_list(Sw2,Sw2L),
	append(Sw1L,Sw2L,MainList),
	list_to_disj(MainList,MainSwitches).


combine_fors(For1,true,For1).

combine_fors(true,For2,For2).

combine_fors(For1,For2,MainFor):-
	conj_to_list(For1,For1L),
	conj_to_list(For2,For2L),
	append(For1L,For2L,ForList),
	list_to_conj(ForList,MainFor).


list_to_disj([H], H) :- !.
list_to_disj([H | T], ';'(H, Conj)) :-
    list_to_disj(T, Conj).

disj_to_list((A;B),[A|T]):- !,disj_to_list(B,T).
disj_to_list(A,[A]):-!.


list_to_conj([],true):-!.
list_to_conj([H], H) :- !.
list_to_conj([H | T], ','(H, Conj)) :-
    list_to_conj(T, Conj).

conj_to_list((A,B),[A|T]):- !,conj_to_list(B,T).
conj_to_list(A,[A]):-!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%	replace_handlers
%
%	replace every handler with its call to the compiled predicate


replace_handlers([]).
replace_handlers([(Head,Body)|T]):-
	(body_contains_handlers(Body,[OneHandler|Handlers]) ->
		make_replace_handlers_by_query([Head],[OneHandler|Handlers],Body,NewBody),
		retract(prog_pred(Head,Body)),
		assert(prog_pred(Head,NewBody))
	;
		true
	),
	replace_handlers(T).


compile_handlers:-
	findall((HN/HA,FArgs,AArgs,MainITEList,HandlerQuery),handler(HN/HA,FArgs,AArgs,MainITEList,HandlerQuery),Handlers),
	make_every_handler(Handlers).



make_every_handler([]).
make_every_handler([(HN/_,FArgs,_,MainITEList,_)|T]):-
	length(VarList,1),
	VarList = [FreshVar],
	handler_me(HN,FreshVar,FArgs,MainITEList,(HHead:- HBody)),
	assert(prog_pred(HHead,HBody)),
	make_every_handler(T).


%%	body_contains_handler(Body,Handler)
%
%	checks if a body contains a handler and unifies the handler
%	with Handler if it exists.

body_contains_handlers(T,[]):-
	var(T),!.

body_contains_handlers((T1,T2),L):- !,
	body_contains_handlers(T1,L1),
	body_contains_handlers(T2,L2),
	append(L1,L2,L).

body_contains_handlers((C -> (T1;T2)),L):- !,
	body_contains_handlers(C,LC),
	body_contains_handlers(T1,L1),
	body_contains_handlers(T2,L2),
	append(L1,L2,LT),
	append(LC,LT,L).


body_contains_handlers((T1;T2),L):- !,
	body_contains_handlers(T1,L1),
	body_contains_handlers(T2,L2),
	append(L1,L2,L).

body_contains_handlers((handle X), [(handle X)]).

body_contains_handlers(_,[]).


%%	make_replace_handlers_by_query(Head,Handlers,Body,NewBody)
%
%	Replaces all the handler in the predicate by their query and asserts
%   the handler itself for further transformation.

make_replace_handlers_by_query(_,[],Body,Body).

make_replace_handlers_by_query(Head,[Handler|Rest],Body,FinalBody):-
	make_handler(Head,Handler,HandlerQuery),
	replace_handler_by_query(Body,Handler,HandlerQuery,NewBody),
	make_replace_handlers_by_query(Head,Rest,NewBody,FinalBody).



replace_handler_by_query(T1,_,_,T1):-
		var(T1),!.

replace_handler_by_query((T1,T2),Handler,Query,(T1R,T2R)):- !,
	replace_handler_by_query(T1,Handler,Query,T1R),
	replace_handler_by_query(T2,Handler,Query,T2R).


replace_handler_by_query((C->(T1;T2)),Handler,Query,(CR->(T1R;T2R))):- !,
	replace_handler_by_query(C,Handler,Query,CR),
	replace_handler_by_query(T1,Handler,Query,T1R),
	replace_handler_by_query(T2,Handler,Query,T2R).


replace_handler_by_query((T1;T2),Handler,Query,(T1R;T2R)):- !,
	replace_handler_by_query(T1,Handler,Query,T1R),
	replace_handler_by_query(T2,Handler,Query,T2R).

replace_handler_by_query((handle X) , (handle X), Query,Query):- !.

replace_handler_by_query(T,_,_,T).


%%	make_handler(Handler,HandlerClause,HandlerQuery)
%
%	generates the handlar's clause and query
%	and asserts them
%

make_handler(HeadList,Handler,HandlerQuery):-
	gensym(handler_,HandlerName),
	get_arguments(Handler,FArgs,AArgs),
	HandlerHead =..[HandlerName,_,_|FArgs],
	add_subsume_handler(HeadList,HandlerHead),
	NewHeadList = [HandlerHead|HeadList],
	get_ite_clauses(NewHeadList,Handler,ITEList),
	get_goal(NewHeadList,Handler,Goal),
	get_finally_clause(Handler,Finally),
	functor(HandlerHead,HN,HA),
	append(Finally,ITEList,MainITEList),
	HandlerQuery=..[HandlerName,_,Goal|AArgs],
	assert(handler(HN/HA,FArgs,AArgs,MainITEList,HandlerQuery)).

get_goal(HeadList,(handle G with _), G1) :- 
	body_contains_handlers(G,[OneHandler|Handlers])->
		make_replace_handlers_by_query(HeadList,[OneHandler|Handlers],G,G1)
		
	;
		G1 = G.

%%	get_arguments(Handler,FArgs,AArgs)
%
%	gets a list of formal args and actual arguments
%
get_arguments((handle _ with _ finally _ for Args), FArgs,AArgs) :-
	Args == true -> (FArgs = [], AArgs= []) ; get_args_list(Args,FArgs,AArgs).

get_arguments((handle _ with _ for Args), FArgs,AArgs) :-
	Args == true -> (FArgs = [], AArgs= []) ; get_args_list(Args,FArgs,AArgs).	

get_arguments((handle _ with _ finally _), [],[]).

get_arguments((handle _ with _ ), [],[]).

get_args_list(Term , [FArg], [AArg]) :-
	\+ var(Term), 
	Term = (FArg = AArg ),
	!.	

get_args_list((Arg) , [Arg],[Arg]) :-
	var(Arg), 
	!.

get_args_list((Term , Rest) , [FArg | T],[AArg | T2]) :- 
	\+ var(Term), 
	Term = (FArg = AArg ),
	!, get_args_list(Rest,T,T2).	

get_args_list((Arg , Rest) , [Arg | T],[Arg | T2]) :- 
	var(Arg),
	!,get_args_list(Rest,T,T2).

%%	get_ite_clauses(Handler,Args)
%
%	gets a list of ITE
%

get_ite_clauses(HeadList,(handle _ with Disjuncts finally _),ITEList) :- 
	get_ite_list(HeadList,Disjuncts,ITEList).

get_ite_clauses(HeadList,(handle _ with Disjuncts for _),ITEList) :- 
	get_ite_list(HeadList,Disjuncts,ITEList).

get_ite_clauses(HeadList,(handle _ with Disjuncts ),ITEList) :- 
	get_ite_list(HeadList,Disjuncts,ITEList).

get_ite_list(HeadList, (A->B), [(A->BG)] ):- 
	(effect(A)->
		 true
		 ;
		 assert(effect(A)),
		 writeclause((A :- shift(A)))
	),
	functor(A,EffectName,EffectAri),
	add_pred_handles(HeadList,EffectName,EffectAri),
	(body_contains_handlers(B,[OneHandler|Handlers])->
		make_replace_handlers_by_query(HeadList,[OneHandler|Handlers],B,BG)
		;
		BG = B
	).

get_ite_list(HeadList, ((A->B); C), [(A->BG)|T] ):-
	(effect(A)->
			 true
			 ;
			 assert(effect(A)),
			 writeclause((A :- shift(A)))
	),
	functor(A,EffectName,EffectAri),
	add_pred_handles(HeadList,EffectName,EffectAri),
	(body_contains_handlers(B,[OneHandler|Handlers])->
		make_replace_handlers_by_query(HeadList,[OneHandler|Handlers],B,BG)
		;
		BG = B
	),
	get_ite_list(HeadList,C,T).



%%	get_finally_clause(Handler,Args)
%
%	gets the finally clause and put it as (finished) that will change
%	afterwards to cont == 0.
%
get_finally_clause((handle _ with _ finally Finally for _), [(finished -> Finallys)]):-
	( body_contains_handlers(Finally,[OneHandler|Handlers]) ->
		make_replace_handlers_by_query([],[OneHandler|Handlers],Finally,Finallys)
		;
		Finally = Finallys
	).
get_finally_clause((handle _ with _ for _), [(finished -> true)]).
get_finally_clause((handle _ with _ finally Finally), [(finished -> Finallys)]):-
	( body_contains_handlers(Finally,[OneHandler|Handlers]) ->
		make_replace_handlers_by_query([],[OneHandler|Handlers],Finally,Finallys)
		;
		Finally = Finallys
	).

get_finally_clause((handle _ with _ ), [(finished -> true)]).


%%	handler_me(Name,Goal,ArgList,ITEList,Clause)
%
%	actual call in order to generate the handler in reset/shift form.
%
handler_me(Name,Goal,ArgList,ITEList,Clause):-
	HeadCall =.. [Name,ParentCont, Goal | ArgList],
	ite_clauses(Name,ParentCont,Cont,Command,ITEList,DisjunctsList),
	ContCall =..[Name,ParentCont,Cont | ArgList],
	Shifter = (shift(Command),ContCall),
	ite_clause(Shifter,DisjunctsList,BodyCall),
	Clause = ( HeadCall :- (reset(Goal,Cont,Command), BodyCall)).

ite_clause(Shifter,[],Shifter).
ite_clause(Shifter,[H|T],(H;T2)) :- 
	ite_clause(Shifter,T,T2).

ite_clauses(_,_,_,_,[],[]).
ite_clauses(Name,ParentCont,Cont,Command,[(Cond->Then)|Tail],[Disjunct|RestDisjunct]):-
	get_disjunct(Name,ParentCont,Cont,Command,Cond,Then,Disjunct),
	ite_clauses(Name,ParentCont,Cont,Command,Tail,RestDisjunct).



get_disjunct(Name,ParentCont,Cont,_,finished,Then,(Cont == 0 -> DisjunctBody)):-
	modify_finally_clause(Name,ParentCont,Cont,Then,DisjunctBody).

get_disjunct(Name,ParentCont,Cont,Command,Cond,Then,(Command = Cond -> DisjunctBody)):-
	get_disjunct_body(Name,ParentCont,Cont,Then,DisjunctBody).


get_disjunct_body(Name,ParentCont,Cont,(T1,T2),(T1R,T2R)):-
	get_disjunct_body(Name,ParentCont,Cont,T1,T1R),
	get_disjunct_body(Name,ParentCont,Cont,T2,T2R).


get_disjunct_body(Name,ParentCont,Cont,(C->(T1;T2)),(CR->(T1R;T2R))):-
	get_disjunct_body(Name,ParentCont,Cont,C,CR),
	get_disjunct_body(Name,ParentCont,Cont,T1,T1R),
	get_disjunct_body(Name,ParentCont,Cont,T2,T2R).

get_disjunct_body(Name,ParentCont,Cont,(T1;T2),(T1R;T2R)):-
	get_disjunct_body(Name,ParentCont,Cont,T1,T1R),
	get_disjunct_body(Name,ParentCont,Cont,T2,T2R).


get_disjunct_body(Name,ParentCont,Cont,(T1),T1R):-
	change_continue_to_call(Name,ParentCont,Cont,T1,T1R).



change_continue_to_call(_,_,_,T,T2):-
	var(T) ,
	T=T2.

change_continue_to_call(Name,ParentCont,Cont,T,T):-
	T =.. [HN,_|Ar],
	name(HN,[104,97,110,100,108,101,114,95|_]),
	HN \= Name,
	T =.. [HN,Cont|Ar].


change_continue_to_call(Name,ParentCont,Cont,T,R):-
	T =..[continue |ArgList],!,
	R =..[Name, ParentCont,Cont | ArgList]. 

change_continue_to_call(_,_,_,T,T).



modify_finally_clause(_,_,_,GF,GF):-
		var(GF),!.

modify_finally_clause(HN,ParentCont,Cont,(G1,G2),(GF1,GF2)):-!,
		modify_finally_clause(HN,ParentCont,Cont,G1,GF1),
		modify_finally_clause(HN,ParentCont,Cont,G2,GF2).

modify_finally_clause(HN,ParentCont,Cont,(G1;G2),(GF1;GF2)):-!,
		modify_finally_clause(HN,ParentCont,Cont,G1,GF1),
		modify_finally_clause(HN,ParentCont,Cont,G2,GF2).

modify_finally_clause(HN,ParentCont,Cont,(C -> (G1;G2)),(CF -> (GF1;GF2))):-!,
		modify_finally_clause(HN,ParentCont,Cont,C,CF),
		modify_finally_clause(HN,ParentCont,Cont,G1,GF1),
		modify_finally_clause(HN,ParentCont,Cont,G2,GF2).

modify_finally_clause(HN,ParentCont,Cont,G,GF):-
	G=..[continue|Args],!,
	subsume_handler(ParentName/_,[HN/_]),
	GF =..[ParentName,_,ParentCont|Args].

modify_finally_clause(_,_,_,G,G).




add_pred_handles([],_,_).
add_pred_handles([H|T],EffectName,EffectAri):- 
	functor(H,HN,HA),
	( pred_handles(HN/HA,L)->
		( member(EffectName/EffectAri, L) ->
		    true
		  ;
		  	retract(pred_handles(HN/HA,L)),
		  	L1 = [EffectName/EffectAri|L],
		  	assert(pred_handles(HN/HA,L1))

		)
	 ;
	 	assert(pred_handles(HN/HA,[EffectName/EffectAri]))
	),
	add_pred_handles(T,EffectName,EffectAri).


add_subsume_handler([],_).
add_subsume_handler([H|T],H2):- 
	functor(H,HN,HA),
    functor(H2,H2N,H2A),
    ( subsume_handler(HN/HA,L)->
		( member(H2N/H2A, L) ->
		    true
		  ;
		  	retract(subsume_handler(HN/HA,L)),
		  	Tmp = [H2N/H2A],
		  	append(L,Tmp,L1),
		  	assert(subsume_handler(HN/HA,L1))

		)
    ;
 		assert(subsume_handler(HN/HA,[H2N/H2A]))	
	),
	add_subsume_handler(T,H2).



write_all_clauses:- 
	findall((Head,Body),prog_pred(Head,Body),List),
	writeclauses(List).

writeclauses([]).
writeclauses([(H,B)|T]):- writeclause((H:-B)), writeclauses(T).

subset_chk([],_).
subset_chk([H|T],L):- member(H,L), subset_chk(T,L).

