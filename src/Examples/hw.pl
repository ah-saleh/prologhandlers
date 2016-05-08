:- effect_list([out/1,choice/1]).

hw:- out(hello), out(world).



example_1:-
	handle hw with (out(X) -> writeln(X), continue).

example_2:-
	handle hw with (out(X) -> continue).

example_3:-
	handle hw with (out(X) -> writeln(X)).

example_4:-
	handle hw with (out(X) -> continue, writeln(X), continue).

example_5:-
	handle hw with (out(X) -> writeln(X), continue)
	finally (writeln(done)).

example_6:-
	handle hw with (out(X) -> writeln(X))
	finally (writeln(done)).


example_7(List):-
	handle hw with
	(out(X)-> Lin=[X|Lmid], continue(Lmid,Lout))
	finally Lin=Lout
	for (Lin = List, Lout = []).

or(G1,G2):-
	choice(B),
	(B==t -> write(G1) ; B==f -> write(G2)).

choose_any(G):- handle G with 
				(choice(B)-> (B = t ; B = f), continue).