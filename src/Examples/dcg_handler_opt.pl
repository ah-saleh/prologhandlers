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
