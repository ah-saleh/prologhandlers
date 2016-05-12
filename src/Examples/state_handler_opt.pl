decr(0) :- !.
decr(A) :-
        A>0,
        get_state(B),
        C is A-1,
        D is B-1,
        put_state(D),
        decr(C).
decr0(0, A, A) :- !.
decr0(A, B, C) :-
        A>0,
        D is A-1,
        E is B-1,
        decr0(D, E, C).
state_handler(A, B, C) :-
        decr0(A, B, C).
