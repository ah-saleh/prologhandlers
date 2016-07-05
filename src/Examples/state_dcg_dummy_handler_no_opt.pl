c(A) :-
        shift(c(A)).
get_state(A) :-
        shift(get_state(A)).
put_state(A) :-
        shift(put_state(A)).
dummy :-
        shift(dummy).
abinc.
abinc :-
        c(a),
        c(b),
        get_state(A),
        B is A+1,
        put_state(B),
        abinc.
inc :-
        get_state(A),
        B is A+1,
        put_state(B).
state_phrase_handler(A, B, C) :-
        handler_0(_, handler_1(_,handler_2(_,abinc),A,B), C, []).
handler_2(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=dummy ->
            handler_2(A, C)
        ;   shift(D),
            handler_2(A, C)
        ).
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
