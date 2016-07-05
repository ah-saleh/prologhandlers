abinc.
abinc :-
        c(a),
        c(b),
        get_state(A),
        B is A+1,
        put_state(B),
        abinc.
abinc0(A, A, [], []).
abinc0(A, B, [a,b|C], []) :-
        D is A+1,
        abinc0(D, B, C, []).
state_phrase_handler(A, B, C) :-
        abinc0(A, B, C, []).
