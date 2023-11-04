------------------------ MODULE wolf_goat_cabbage --------------------------
\* Importing certain functionality, like import in Java.
EXTENDS Integers, TLC

\* theses are the constants that we can supply in cfg file.
\* CONSTANTS

Goat == "goat"
Farmer == "farmer"
Cabbage == "cabbage"
Wolf == "wolf"
PossibleActors == {Goat, Farmer, Cabbage, Wolf}

\* pluscal block written in a comments as this is still a TLA+ file.
\* This will get translated into actual TLA+ underneath.
(* --algorithm wolf_goat_cabbage {
    variables   startSide = PossibleActors; 
                endSide = {};
    define {
        TypeOK == /\ \A a \in startSide: a \in PossibleActors 
                  /\ \A a \in endSide: a \in PossibleActors

        Inv1 == startSide \cap endSide = {}

        Inv2 == startSide \cup endSide = PossibleActors

        Inv3 == \neg (startSide = {} /\ endSide = PossibleActors)

        \*Inv == /\ Inv1 /\ Inv2 /\ Inv3
        
        \* Terminate == [] \neg (startSide = {}
        \*             /\ endSide = PossibleActors)             

        isAtStart(a) == a \in startSide

        isAtEnd(a) == a \in endSide

        exists(a) == isAtStart(a) \/ isAtEnd(a)

        areTogether(a1, a2) == (isAtStart(a1) /\ isAtStart(a2)) \/ (isAtEnd(a1) /\ isAtEnd(a2))

        findTogether(a) == { b \in PossibleActors : areTogether(a, b)} \ {a}

        isWithoutFarmer(a) == \neg areTogether(a, Farmer)

    }

    \* No real need for process here as we only have one process globally
    \* fair here does not do anything
    fair process (FarmerProc = 1) {
F1:
        while(startSide # {}){
            either {
                await isAtStart(Farmer) /\ findTogether(Farmer) # {};
                with (a \in findTogether(Farmer)){
                    startSide := startSide \ {Farmer, a};
                    endSide := endSide \cup {Farmer, a};
                }

            } or {
                await isAtEnd(Farmer) /\ findTogether(Farmer) # {};
                with (a \in findTogether(Farmer)){
                    startSide := startSide \cup {Farmer, a};
                    endSide := endSide \ {Farmer, a};
                }
            } or {
                \* Farmer can move to another side wihtout taking anyone if
                \* the other side is not empty. Emptiness check is to stop
                \* infinite loop.
                await isAtStart(Farmer) /\ endSide # {};
                startSide := startSide \ {Farmer};
                endSide := endSide \cup {Farmer};
            } or {
                \* Same as previous, but in opposite direction
                await isAtEnd(Farmer) /\ startSide # {};
                startSide := startSide \cup {Farmer};
                endSide := endSide \ {Farmer};
            };
            \* Wolf eating goat.
            \* I was thinking of making this a separate process, but I don't
            \* know how to stop infinite loop.
W1:         if (isWithoutFarmer(Wolf) /\ areTogether(Wolf, Goat)){
                startSide := startSide \ {Goat};
                endSide := endSide \ {Goat};
            };
            \* Goat eating cabbage.
G1:         if (exists(Goat) /\ isWithoutFarmer(Goat) /\ areTogether(Goat, Cabbage)){
                startSide := startSide \ {Cabbage};
                endSide := endSide \ {Cabbage};
            };
        }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "60a80568" /\ chksum(tla) = "b48624a7")
VARIABLES startSide, endSide, pc

(* define statement *)
TypeOK == /\ \A a \in startSide: a \in PossibleActors
          /\ \A a \in endSide: a \in PossibleActors

Inv1 == startSide \cap endSide = {}

Inv2 == startSide \cup endSide = PossibleActors

Inv3 == \neg (startSide = {} /\ endSide = PossibleActors)






isAtStart(a) == a \in startSide

isAtEnd(a) == a \in endSide

exists(a) == isAtStart(a) \/ isAtEnd(a)

areTogether(a1, a2) == (isAtStart(a1) /\ isAtStart(a2)) \/ (isAtEnd(a1) /\ isAtEnd(a2))

findTogether(a) == { b \in PossibleActors : areTogether(a, b)} \ {a}

isWithoutFarmer(a) == \neg areTogether(a, Farmer)


vars == << startSide, endSide, pc >>

ProcSet == {1}

Init == (* Global variables *)
        /\ startSide = PossibleActors
        /\ endSide = {}
        /\ pc = [self \in ProcSet |-> "F1"]

F1 == /\ pc[1] = "F1"
      /\ IF startSide # {}
            THEN /\ \/ /\ isAtStart(Farmer) /\ findTogether(Farmer) # {}
                       /\ \E a \in findTogether(Farmer):
                            /\ startSide' = startSide \ {Farmer, a}
                            /\ endSide' = (endSide \cup {Farmer, a})
                    \/ /\ isAtEnd(Farmer) /\ findTogether(Farmer) # {}
                       /\ \E a \in findTogether(Farmer):
                            /\ startSide' = (startSide \cup {Farmer, a})
                            /\ endSide' = endSide \ {Farmer, a}
                    \/ /\ isAtStart(Farmer) /\ endSide # {}
                       /\ startSide' = startSide \ {Farmer}
                       /\ endSide' = (endSide \cup {Farmer})
                    \/ /\ isAtEnd(Farmer) /\ startSide # {}
                       /\ startSide' = (startSide \cup {Farmer})
                       /\ endSide' = endSide \ {Farmer}
                 /\ pc' = [pc EXCEPT ![1] = "W1"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                 /\ UNCHANGED << startSide, endSide >>

W1 == /\ pc[1] = "W1"
      /\ IF isWithoutFarmer(Wolf) /\ areTogether(Wolf, Goat)
            THEN /\ startSide' = startSide \ {Goat}
                 /\ endSide' = endSide \ {Goat}
            ELSE /\ TRUE
                 /\ UNCHANGED << startSide, endSide >>
      /\ pc' = [pc EXCEPT ![1] = "G1"]

G1 == /\ pc[1] = "G1"
      /\ IF exists(Goat) /\ isWithoutFarmer(Goat) /\ areTogether(Goat, Cabbage)
            THEN /\ startSide' = startSide \ {Cabbage}
                 /\ endSide' = endSide \ {Cabbage}
            ELSE /\ TRUE
                 /\ UNCHANGED << startSide, endSide >>
      /\ pc' = [pc EXCEPT ![1] = "F1"]

FarmerProc == F1 \/ W1 \/ G1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == FarmerProc
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(FarmerProc)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

















=================================================

https://en.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem

A farmer with a wolf, a goat, and a cabbage must cross a river by boat. 
The boat can carry only the farmer and a single item. If left unattended together,
the wolf would eat the goat, or the goat would eat the cabbage.
How can they cross the river without anything being eaten?

Do I model two sides of the river? Like start and end? Each is a set or list.
Initially start has famer, worlf, goat, cabbage. I want to check if it is 
possible that all can end up at the end. I model all the rules to restict the
movement.

About the solution. It doesn't feel optimal or minimal. Here I directly model
all the possible transitions, and then find the solution by making a bait 
invariant. This way I don't model the solution, but I model the problem isAtEnd
take advantage of TLC to search the state space for solution. But looking 
another way I am still checking the property of the problem, I am checking if
solution is possible or not.  

