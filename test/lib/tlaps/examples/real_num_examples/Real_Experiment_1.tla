------------------------- MODULE Real_Experiment_1 -------------------------
EXTENDS TLAPS, Reals, Integers

\* Theorems that can be proved
\* THEOREM 1 + 1 = 2 BY Z3
\* THEOREM 1.0 + 1.0 = 2.0 BY Z3
\* THEOREM 2^3 = 8 BY Z3 
\* THEOREM 2%2=0 BY Z3 
\* THEOREM 2/2=1 BY Z3 
\* THEOREM 1.0*1.0 = 1.0 BY Z3
\* THEOREM \E x \in Int: x%x = 0 BY Z3 
\* THEOREM \E x \in Real: x + 1.0 = 2.0 BY Z3
\* THEOREM \E x \in Int: 2%x = 2 BY Z3 
\* THEOREM \E x \in Real: 1.0=x/1.0 BY Z3
\* THEOREM \E x,y,z \in Real: x + y =  z BY Z3
\* THEOREM \E x \in Int: x * 2 = 2 BY Z3
\* THEOREM \E x,y,z \in Int: x + (y + x) = z BY Z3 
\* THEOREM (1.0 + 1.0)*1.0 = 2.0 BY Z3 
\* THEOREM \E x \in Real: x*x - 1.0 = 0.0 BY Z3 
\* THEOREM \E x,y \in Int: y + (1 \div 1) = x BY Z3
\* THEOREM \E x \in Int: x*x - 9 = 0 BY Z3 
\* THEOREM \E x \in Int: x + (x*1) = 2 BY Z3 
\* THEOREM \E x,y,a,b \in Real: ((x*x)+(y*y))*((x-b)*(x-b)) = a*a*x*x BY Z3
\* THEOREM \E x,a,y \in Real : x*x*x*x = a*a * ((x*x) + (y*y)) BY Z3
\* THEOREM \E x,y,z \in Int: x + (y + x) = z BY Z3 
\* THEOREM \E x \in Int: x + (x*1) = 2 BY Z3 
\* THEOREM \E x \in Real: x*x - 1.0 = 0.0 BY Z3 
\* THEOREM \E x \in Real: x - 1.0/2.0 = 1.0/2.0 BY Z3 
\* THEOREM \E x \in Real : x * x * x - 3.0 * x * (x - 1.0) - 1.0 = 0.0 BY Z3
\* THEOREM \A x,y,z \in Real : x*x + y*y + z*z <= 1.0 /\ (x-2.0)*(x-2.0) + (y-2.0)*(y-2.0) + (z-2.0)*(z-2.0) <= 1.0 => 1.0 = 0.0 BY Z3
\* THEOREM \E x \in (-5..5): x - 5 = 0 BY Z3
\* THEOREM \E x \in (-5.0..5.0): x*x - 5.0 = 0.0 BY Z3 
\* THEOREM \E x \in Int: x \div 2 = 2 BY Z3
\* THEOREM \E x \in Int: x -(-2) = -2 BY Z3
\* THEOREM \E x \in Real: x -(-2.0) = -2.0 BY Z3
\* THEOREM \A x,y \in Real : ~((x < -2.0) /\ (x*x + y*y <= 4.0 /\ x*x + y*y >= 1.0)) BY Z3 
\* THEOREM \A x,y \in Real: ((-0.5 <= x /\ x <= 0.5 /\ 1.0 <= y /\ y <= 1.5) => ((x*x)+(y*y) <= 4.0 /\ (x*x)+(y*y) >= 1.0)) BY Z3
\* THEOREM \E x,y \in Real: 1.0/(x*x) > 0.0 BY Z3 
\* THEOREM \E x \in Real: x >= 0.0 BY Z3
\* THEOREM \A x \in Real: x*x >=0.0 BY Z3
\* THEOREM \A x \in Int: x*x >= 0 BY Z3

\* \* Theorems that should fail and pass context generation
\* THEOREM 1 + 1.0 = 2 BY Z3
\* THEOREM 1 - 1 = 2 BY Z3
\* THEOREM 2%2=1 BY Z3
\* THEOREM \E x \in Real: x*x + 1.5 = 0 BY Z3
\* THEOREM \E x \in Int: x/0 = x BY Z3
\* THEOREM \E y \in Int: y + (0/0) = y BY Z3
\* THEOREM \E y \in Int: y + (1/1) = y BY Z3
\* THEOREM \E x \in Real: x*x - 1 = 0 BY Z3
\* THEOREM \A x,y \in Real: ((-0.5 <= x /\ x <= 0.5 /\ 1 <= y /\ y <= 1.5) => ((x*x)+(y*y) <= 4 /\ (x*x)+(y*y) >= 1)) BY Z3
\* THEOREM \E x \in Int: x + 1/2 = 1/2 BY Z3
\* THEOREM \E x \in Int: x^2 = 4 BY Z3
\* THEOREM \E x \in Real: x^(2.0/2.0) = 2.0 BY Z3
\* THEOREM \E x \in Real: x%2.0 = 2.0 BY Z3
\* THEOREM \E x \in Real: 2.0%x = 2.0 BY Z3
\* THEOREM \E x \in Real: x \div 2.0 = 2.0 BY Z3
\* THEOREM \E x \in Int: x - 1.0 = 0 BY Z3
\* THEOREM \E x \in Real: x - 0 = 1.0 BY Z3
\* THEOREM \E x,y \in Real: x + (x*1) = y BY Z3
\* THEOREM \E x \in Int: x + 2.1 = 2.1 BY Z3
\* THEOREM \A x \in Real: x*x >= 0 \/ \A x \in Int: x*x >= 0.0 BY Z3
\* THEOREM (\A x \in Int: x*x >= 0) /\ (\A x \in Real: x*x >= 0.0) BY Z3
\* THEOREM 2%3 = 2.0 BY Z3

\* \* Theorems that fail and fail context generation
\* THEOREM \A x \in Real: x*"a" = 0 BY Z3
\* THEOREM \E x \in Real: x + Infinity = 1 + Infinity BY Z3

=============================================================================
\* Modification History
\* Last modified Wed Sep 13 08:25:36 IST 2023 by ovini
\* Created Wed Sep 13 08:24:19 IST 2023 by ovini
