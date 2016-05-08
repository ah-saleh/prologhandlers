out(A) :-
        shift(out(A)).
choice(A) :-
        shift(choice(A)).
hw :-
        out(hello),
        out(world).
or(A, B) :-
        choice(C),
        (   C==t ->
            write(A)
        ;   C==f ->
            write(B)
        ).
example_1 :-
        handler_0(_, hw).
example_2 :-
        handler_1(_, hw).
example_3 :-
        handler_2(_, hw).
example_4 :-
        handler_3(_, hw).
example_5 :-
        handler_4(_, hw).
example_6 :-
        handler_5(_, hw).
example_7(A) :-
        handler_6(_, hw, A, []).
choose_any(A) :-
        handler_7(_, A).
handler_0(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=out(E) ->
            writeln(E),
            handler_0(A, C)
        ;   shift(D),
            handler_0(A, C)
        ).
handler_1(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=out(_) ->
            handler_1(A, C)
        ;   shift(D),
            handler_1(A, C)
        ).
handler_2(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=out(E) ->
            writeln(E)
        ;   shift(D),
            handler_2(A, C)
        ).
handler_3(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=out(E) ->
            handler_3(A, C),
            writeln(E),
            handler_3(A, C)
        ;   shift(D),
            handler_3(A, C)
        ).
handler_4(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            writeln(done)
        ;   D=out(E) ->
            writeln(E),
            handler_4(A, C)
        ;   shift(D),
            handler_4(A, C)
        ).
handler_5(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            writeln(done)
        ;   D=out(E) ->
            writeln(E)
        ;   shift(D),
            handler_5(A, C)
        ).
handler_6(A, B, C, D) :-
        reset(B, E, F),
        (   E==0 ->
            C=D
        ;   F=out(G) ->
            C=[G|H],
            handler_6(A, E, H, D)
        ;   shift(F),
            handler_6(A, E, C, D)
        ).
handler_7(A, B) :-
        reset(B, C, D),
        (   C==0 ->
            true
        ;   D=choice(E) ->
            (   E=t
            ;   E=f
            ),
            handler_7(A, C)
        ;   shift(D),
            handler_7(A, C)
        ).
