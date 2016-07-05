ab.
ab :-
        c(a),
        c(b),
        ab.
ab0(A, A).
ab0([a,b|A], B) :-
        ab0(A, B).
phrase_ab(A, B) :-
        ab0(A, B).


test(ListLength):-
	generate_ab(ListLength,[],List),
	statistics(runtime,[T1,_]),
	phrase_ab(List,[]),
	statistics(runtime,[T2,_]),
	Time is T2 - T1,
	write('Time is :- '), write(Time),nl.