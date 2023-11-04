------------------------ MODULE wolf_goat_cabbage_short ----------------------

EXTENDS FiniteSets

CONSTANT Goat, Cabbage, Wolf, Man

All == {Goat, Cabbage, Wolf, Man}

ASSUME Cardinality(All) = 4

\* L for left side
VARIABLE L

Init == L = All
\* R for right side
R == All \ L

Safe(s) == 
    /\ {Goat, Cabbage} \subseteq s => Man \in s
    /\ {Goat, Wolf} \subseteq s => Man \in s

TypeInv == L \subseteq All /\ Safe(L) /\ Safe(R)

Move(x) == 
    /\ \/ /\ {x, Man} \subseteq L
          /\ L' = L \ {x, Man}
       \/ /\ {x, Man} \subseteq R
          /\ L' = L \union {x, Man}
    /\ Safe(L')
    /\ Safe(R')

\* Note that here we allow x == Man, so we allow Man to travel alone, which is essential
Next == \E x \in All: Move(x)

Prog == Init /\ [][Next]_L

Impossible == [](R # All)

===============================================================================
Credits to https://muratbuffalo.blogspot.com/2023/10/cabbage-goat-and-wolf-puzzle-in-tla.html
