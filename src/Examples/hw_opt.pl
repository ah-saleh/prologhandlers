hw :-
        out(hello),
        out(world).
hw0 :-
        writeln(hello),
        writeln(world).
example_1 :-
        hw0.
hw1.
example_2 :-
        hw1.
hw2 :-
        writeln(hello).
example_3 :-
        hw2.
hw3 :-
        writeln(world),
        writeln(hello),
        writeln(world).
example_4 :-
        hw3.
hw4 :-
        writeln(hello),
        writeln(world),
        writeln(done).
example_5 :-
        hw4.
hw5 :-
        writeln(hello).
example_6 :-
        hw5.
