---------------------- MODULE wolf_goat_cabbage_muratbuffalo ------------------

EXTENDS Integers, TLC, FiniteSets

Sides == {1,2}
C == "Cabbage"
G == "Goat"
W == "Wolf"
F == "Farmer"

Allowed(S) == 
    \/ F \in S
    \/ (
        /\ ~ (C \in S /\ G \in S)
        /\ ~ (G \in S /\ W \in S)
        )


(* --algorithm CabbageGoatWolf {
    variables
        banks = << {C,G,W,F}, {} >>;
        boat = {};

    define {
        TypeOK == 
            /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
            /\ Cardinality(boat) <= 2
            /\ boat \in SUBSET {F,C,G,W}
            /\ banks[1] \in SUBSET {F,C,G,W}
            /\ banks[2] \in SUBSET {F,C,G,W}
        
        \* We use an inverse here as we want TLC to show us the solution which
        \* is a couterexample
        NotSolved == Cardinality(banks[2]) < 4


        \* Note that we allow farmer to go alone on a boat, this is necessary
        \* for solution
        SafeBoats(s) ==
            {
                B \in SUBSET banks[s]:
                    /\ F \in B
                    /\ Cardinality(B) <= 2
                    /\ Allowed(banks[s] \ B) 
            }

    }

    fair process (Bank \in Sides) {
S:      while (TRUE) {
            either { \* LOAD
                await (banks[self]#{} /\ boat={});
                \* here we checks for all possible safe boats.
                \* "The randomness, which comes from the *with* keyword, enables
                \* the model checker to explore all behaviors allowed by the 
                \* SafeBoats definition. "
                with (P \in SafeBoats(self)) {
                    boat := P;
                    banks[self] := banks[self] \ P;
                }

            } or { \* UNLOAD
                \* Note that here we allow to infinitely load and unload from
                \* the same side, but this is fine as we are looking for
                \* counterexample.
                await (boat#{});
                banks[self] := banks[self] \union boat;
                boat := {};
            }
        }    
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cf77bd9f" /\ chksum(tla) = "83c3f94e")
VARIABLES banks, boat

(* define statement *)
TypeOK ==
    /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
    /\ Cardinality(boat) <= 2
    /\ boat \in SUBSET {F,C,G,W}
    /\ banks[1] \in SUBSET {F,C,G,W}
    /\ banks[2] \in SUBSET {F,C,G,W}



NotSolved == Cardinality(banks[2]) < 4




SafeBoats(s) ==
    {
        B \in SUBSET banks[s]:
            /\ F \in B
            /\ Cardinality(B) <= 2
            /\ Allowed(banks[s] \ B)
    }


vars == << banks, boat >>

ProcSet == (Sides)

Init == (* Global variables *)
        /\ banks = << {C,G,W,F}, {} >>
        /\ boat = {}

Bank(self) == \/ /\ (banks[self]#{} /\ boat={})
                 /\ \E P \in SafeBoats(self):
                      /\ boat' = P
                      /\ banks' = [banks EXCEPT ![self] = banks[self] \ P]
              \/ /\ (boat#{})
                 /\ banks' = [banks EXCEPT ![self] = banks[self] \union boat]
                 /\ boat' = {}

Next == (\E self \in Sides: Bank(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Sides : WF_vars(Bank(self))

\* END TRANSLATION 










===============================================================================
See https://muratbuffalo.blogspot.com/2023/10/cabbage-goat-and-wolf-puzzle-in-tla.html





