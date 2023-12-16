------------------------- MODULE RealsIntsTestFail -------------------------
EXTENDS TLAPS, Reals, Integers

\* Theorems that fail
THEOREM 1 + 1.0 = 2 BY Z3
THEOREM \E x \in Real: 2.0^(1.0/2.0) = x BY Z3
THEOREM 1 - 1 = 2 BY Z3
THEOREM 2%2=1 BY Z3
THEOREM \E x \in Real: x*x + 1.5 = 0 BY Z3
THEOREM \E x \in Int: x/0 = x BY Z3
THEOREM \E y \in Int: y + (0/0) = y BY Z3
THEOREM \E y \in Int: y + (1/1) = y BY Z3
THEOREM \E x \in Real: x*x - 1 = 0 BY Z3
THEOREM \A x,y \in Real: ((-0.5 <= x /\ x <= 0.5 /\ 1 <= y /\ y <= 1.5) => ((x*x)+(y*y) <= 4 /\ (x*x)+(y*y) >= 1)) BY Z3
THEOREM \E x \in Int: x + 1/2 = 1/2 BY Z3
THEOREM \E x \in Int: x^2 = 4 BY Z3
THEOREM \E x \in Real: x^(2.0/2.0) = 2.0 BY Z3
THEOREM \E x \in Real: x%2.0 = 2.0 BY Z3
THEOREM \E x \in Real: 2.0%x = 2.0 BY Z3
THEOREM \E x \in Real: x \div 2.0 = 2.0 BY Z3
THEOREM \E x \in Int: x - 1.0 = 0 BY Z3
THEOREM \E x \in Real: x - 0 = 1.0 BY Z3
THEOREM \E x,y \in Real: x + (x*1) = y BY Z3
THEOREM \E x \in Int: x + 2.1 = 2.1 BY Z3
THEOREM 2%3 = 2.0 BY Z3
THEOREM \E x \in Real: x^2.0 = 4.0 BY Z3
THEOREM \A x \in Real: x*"a" = 0 BY Z3
THEOREM \E x \in Real: x + Infinity = 1 + Infinity BY Z3
=============================================================================
\* Modification History
\* Last modified Mon Nov 27 13:58:02 GMT 2023 by ovini
\* Created Mon Nov 27 13:55:37 GMT 2023 by ovini
