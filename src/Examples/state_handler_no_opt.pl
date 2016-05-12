get_state(A) :-
        shift(get_state(A)).
put_state(A) :-
        shift(put_state(A)).
decr(0) :- !.
decr(A) :-
        A>0,
        get_state(B),
        C is B-1,
        put_state(C),
        D is A-1,
        decr(D).
state_handler(A, B, C) :-
        handler_0(_, decr(A), B, C).
handler_0(A, B, C, D) :-
        reset(B, E, F),
        (   E==0 ->
            G=H
        ;   F=get_state(I) ->
            I=H,
            handler_0(A, E, H, G)
        ;   F=put_state(J) ->
            handler_0(A, E, J, G)
        ;   shift(F),
            handler_0(A, E, C, D)
        ).
