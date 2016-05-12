:- effect_list([c/1]).

ab.
ab:- c(a), c(b),ab.

phrase_ab(Lin,Lout):-
	handle
		ab
	with
		(c(I)-> Lin1 = [I|Lmid], continue(Lmid,Lout1))
	finally
		Lin1 = Lout1
	for 
		(Lin1 = Lin, Lout1 = Lout).