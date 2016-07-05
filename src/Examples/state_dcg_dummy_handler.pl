/*************************************
Definite Clause Grammar with Mutable States and a dummy handler Benchmark

To run the program : 

1) Using sicstus prolog run the following query:

?- consult('../CompilerWithEffects.pl').

2) in order to generate the non-optimized version of the program:

?- compile_effects('state_dcg_handler.pl',false,'state_dcg_handler_no_opt.pl').

Or, to generate the optimized version:

?- compile_effects('state_dcg_handler.pl',true,'state_dcg_handler_opt.pl').


3) The compiler generates the new file. Run the newly generated file with
   hProlog (recommended) or SWI-Prolog.

4) Add the following program clauses in order to generate the benchmarks :

*******

generate_ab(I,N,N):- I =< 0, !.
generate_ab(N,T,T2):- N1 is N-2, 
                      generate_ab(N1,[a,b|T],T2).



test(ListLength):-
	generate_ab(ListLength,[],List),
	statistics(runtime,[T1,_]),
	state_phrase_handler(0,_,ListLength),
	statistics(runtime,[T2,_]),
	Time is T2 - T1,
	write('Time is :- '), write(Time),nl.


*******

5) the Predicate test/1 is the benchmark testing predicate.
ListLength is the variable of the size of the input list. Run the benchmark
with the wanted list length. 
**************************************/


:- effect_list([get_state/1,put_state/1,c/1,dummy/0]).


abinc.
abinc :- c(a), c(b), get_state(St), St1 is St+1, put_state(St1), abinc.

inc :- get_state(St), St1 is St+1, put_state(St1).


state_phrase_handler(Sinn,Soutt,Linn) :- 
						handle
							(handle (handle
									(abinc) with
									(dummy -> continue)
									) with
							( get_state(Q) -> Q = Sin, continue(Sin,Sout)
							; put_state(NS) -> continue(NS,Sout)
							)
							finally Sout = Sin
							for (Sin = Sinn,Sout = Soutt))
						with
						(c(X) -> Lin = [X|Lmid], continue(Lmid,Lout))
						finally Lin = Lout
						for( Lin=Linn, Lout=[]).