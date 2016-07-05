c(A) :-
        shift(c(A)).
get_state(A) :-
        shift(get_state(A)).
put_state(A) :-
        shift(put_state(A)).
abinc.
abinc :-
        c(a),
        c(b),
        get_state(A),
        B is A+1,
        put_state(B),
        abinc.
state_phrase_handler(A, B, C) :-
        handler_0(_, handler_1(_,abinc,A,B), C, []).
handler_1(A, B, C, D) :-
        reset(B, E, F),
        (   E==0 ->
            D=C
        ;   F=get_state(G) ->
            G=C,
            handler_1(A, E, C, D)
        ;   F=put_state(H) ->
            handler_1(A, E, H, D)
        ;   shift(F),
            handler_1(A, E, C, D)
        ).
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
