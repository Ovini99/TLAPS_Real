---------------------------- MODULE RealNumExample2 ----------------------------
EXTENDS TLAPS, Reals

THEOREM \A x,y \in Real : ~((x < -2) /\ (x*x + y*y <= 4 /\ x*x + y*y >= 1)) BY Z3
=============================================================================



