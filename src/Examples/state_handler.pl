:- effect_list([get_state/1,put_state/1]).

decr(0):- !.
decr(N):- N>0, get_state(S), N1 is N - 1, S1 is S-1, put_state(S1), decr(N1).

state_handler(N,Sin,Sout):-
	handle 
  		decr(N) 
  	with
		( get_state(Q) -> Q = Sin1, continue(Sin1,Sout1)
		; put_state(NS) -> continue(NS,Sout1)
		)
	finally 
		Sout1 = Sin1
	for 
		(Sin1=Sin,Sout1=Sout).