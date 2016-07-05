c(A) :-
        shift(c(A)).
ab.
ab :-
        c(a),
        c(b),
        ab.
phrase_ab(A, B) :-
        handler_0(_, ab, A, B).
handler_0(A, B, C, D) :-
        reset(B, E, F),
        (   E==0 ->
            C=D
        ;   F=c(G) ->
            C=[G|H],
            handler_0(A, E, H, D)
        ;   shift(F),
            handler_0(A, E, C, D)
        ).


test(ListLength):-
    generate_ab(ListLength,[],List),
    statistics(runtime,[T1,_]),
    phrase_ab(List,[]),
    statistics(runtime,[T2,_]),
    Time is T2 - T1,
    write('Time is :- '), write(Time),nl.