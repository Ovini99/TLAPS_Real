---------------------------- MODULE RealNumExample1 ----------------------------
EXTENDS TLAPS, Reals

THEOREM \A x,y \in Real: ((-0.5 <= x /\ x <= 0.5 /\ 1 <= y /\ y <= 1.5) => ((x*x)+(y*y) <= 4 /\ (x*x)+(y*y) >= 1)) BY Z3
\* THEOREM \A x,y \in Real: ((-0.5 <= x /\ x <= 0.5 /\ 1 <= y /\ y <= 1.5) => ((x*x)+(y*y) <= 4 /\ (x*x)+(y*y) >= 1)) BY METIT
=============================================================================



