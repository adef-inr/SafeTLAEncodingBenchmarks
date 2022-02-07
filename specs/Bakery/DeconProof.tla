----------------------------- MODULE DeconProof ----------------------------
(***************************************************************************)
(* Proofs for the deconstructed Bakery.                                    *)
(***************************************************************************)
EXTENDS BakeryDeconstructed, TLAPS

USE NAssump

(***************************************************************************)
(* The provers have a hard time with the process identifiers, and we help  *)
(* them by proving utility lemmas.                                         *)
(***************************************************************************)
LEMMA DisjointIds ==
  /\ ProcIds \cap SubProcs = {}
  /\ ProcIds \cap WrProcs = {}
  /\ SubProcs \cap WrProcs = {}
BY DEF ProcIds, SubProcs, WrProcs

LEMMA ProcId ==
  ASSUME NEW i \in Procs
  PROVE  /\ <<i>> \in ProcIds
         /\ <<i>> \notin SubProcs
         /\ <<i>> \notin WrProcs
BY DEF ProcIds, SubProcs, WrProcs

LEMMA SubProcId ==
  ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
  PROVE  /\ <<i,j>> \in SubProcs
         /\ <<i,j>> \notin ProcIds
         /\ <<i,j>> \notin WrProcs
         /\ <<i,j,"wr">> \in WrProcs
         /\ <<i,j,"wr">> \notin SubProcs
         /\ <<i,j,"wr">> \notin ProcIds
BY DEF ProcIds, SubProcs, WrProcs, OtherProcs

LEMMA qmNotNat == qm \notin Nat
BY NoSetContainsEverything DEF qm

(***************************************************************************)
(* The TypeOK predicate does not quite assert the types of the variables   *)
(* localNum and localCh, and it doesn't cover the types of the local       *)
(* variables. The following predicate is more precise.                     *)
(***************************************************************************)
PFunc(X,Y) ==
  \* partial functions from X to Y
  UNION {[XX -> Y] : XX \in SUBSET X}
POP(S) ==
  \* set of functions [i \in Procs -> [OtherProcs(i) -> S]]
  {f \in [Procs -> PFunc(Procs,S)] :
     \A i \in Procs : DOMAIN f[i] = OtherProcs(i)}

LEMMA POP_construct ==
  ASSUME NEW S, NEW s \in S
  PROVE  [p \in Procs |-> [q \in OtherProcs(p) |-> s]] \in POP(S)
<1>. DEFINE f(p) == [q \in Procs \ {p} |-> s]
<1>1. ASSUME NEW p \in Procs
      PROVE  /\ f(p) \in PFunc(Procs, S)
             /\ DOMAIN f(p) = OtherProcs(p)
  BY (*Isa*) DEF PFunc, OtherProcs
<1>. QED  BY <1>1(*, Zenon*) DEF POP

LEMMA POP_access ==
  ASSUME NEW S, NEW f \in POP(S),
         NEW p \in Procs, NEW q \in OtherProcs(p)
  PROVE  f[p][q] \in S
BY DEF POP, PFunc

LEMMA POP_except ==
  ASSUME NEW S, NEW f \in POP(S),
         NEW p \in Procs, NEW q \in OtherProcs(p), NEW s \in S 
  PROVE  /\ [f EXCEPT ![p][q] = s] \in POP(S)
         /\ [f EXCEPT ![p][q] = s][p][q] = s
         /\ \A pp \in Procs : \A qq \in OtherProcs(pp) :
               pp # p \/ qq # q => [f EXCEPT ![p][q] = s][pp][qq] = f[pp][qq]
BY DEF POP, PFunc, OtherProcs

FullTypeOK ==
  /\ number \in [Procs -> Nat]
  /\ localNum \in POP(Nat \cup {qm})
  /\ localCh \in POP({0,1})
  /\ pc \in [ProcIds \cup SubProcs \cup WrProcs ->
               {"ncs", "M", "M0", "L", "cs", "P",
                "ch", "test", "Lb", "L2", "L3",
                "wr"}]
  /\ \A i \in ProcIds : pc[i] \in {"ncs", "M", "M0", "L", "cs", "P"}
  /\ \A i \in SubProcs : pc[i] \in {"ch", "test", "Lb", "L2", "L3"}
  /\ \A i \in WrProcs : pc[i] = "wr"
  /\ unRead \in [ProcIds -> SUBSET Procs]
  /\ \A i \in ProcIds : unRead[i] \in SUBSET OtherProcs(i[1])
  /\ v \in [ProcIds -> Nat]

THEOREM Typing == Spec => []FullTypeOK
<1>1. Init => FullTypeOK
  <2> SUFFICES ASSUME Init
               PROVE  FullTypeOK
    OBVIOUS
  <2>1. /\ localNum \in POP(Nat \cup {qm})
        /\ localCh \in POP({0,1})
    BY POP_construct(*, Zenon*) DEF Init
  <2>. QED
    BY <2>1, DisjointIds DEF Init, ProcSet, FullTypeOK
<1>2. FullTypeOK /\ [Next]_vars => FullTypeOK'
  <2> SUFFICES ASSUME FullTypeOK,
                      [Next]_vars
               PROVE  FullTypeOK'
    OBVIOUS
  <2>. USE DEF FullTypeOK
  <2>1. ASSUME NEW self \in ProcIds,
               ncs(self)
        PROVE  FullTypeOK'
    BY <2>1 DEF ncs
  <2>2. ASSUME NEW self \in ProcIds,
               M(self)
        PROVE  FullTypeOK'
    BY <2>2 DEF M, OtherProcs
  <2>3. ASSUME NEW self \in ProcIds,
               M0(self)
        PROVE  FullTypeOK'
    <3>1. CASE unRead[self] # {}
      <4>. PICK j \in unRead[self] :
                /\ IF localNum[self[1]][j] # qm
                   THEN v' = [v EXCEPT ![self] = Max(v[self], localNum[self[1]][j])]
                   ELSE v' = v
                /\ unRead' = [unRead EXCEPT ![self] = unRead[self] \ {j}]
                /\ pc' = [pc EXCEPT ![self] = "M0"]
                /\ UNCHANGED << number, localNum, localCh >>
        BY <2>3, <3>1 DEF M0
      <4>. (v \in [ProcIds -> Nat])'
        <5>1. CASE localNum[self[1]][j] = qm
          BY <5>1
        <5>2. CASE localNum[self[1]][j] # qm
          BY <5>2 DEF Max, POP, PFunc, ProcIds
        <5>. QED  BY <5>1, <5>2
      <4>. QED
        OBVIOUS (*BY Zenon*)
    <3>2. CASE unRead[self] = {}
      <4>. PICK n \in Nat :
                /\ n > v[self]
                /\ number' = [number EXCEPT ![self[1]] = n]
                /\ localNum' = [j \in Procs |->
                                      [i \in OtherProcs(j) |->
                                             IF i = self[1] THEN qm
                                                            ELSE localNum[j][i]]]
                /\ v' = [v EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "L"]
                /\ UNCHANGED <<unRead, localCh>>
        BY <2>3, <3>2 DEF M0
      <4>. (number \in [Procs -> Nat])'
        OBVIOUS (*BY Zenon*)
      <4>. QED
        BY DEF POP, PFunc
    <3>. QED  BY <3>1, <3>2
  <2>4. ASSUME NEW self \in ProcIds,
               L(self)
        PROVE  FullTypeOK'
    BY <2>4 DEF L
  <2>5. ASSUME NEW self \in ProcIds,
               cs(self)
        PROVE  FullTypeOK'
    BY <2>5 DEF cs
  <2>6. ASSUME NEW self \in ProcIds,
               P(self)
        PROVE  FullTypeOK'
    <3>. (number \in [Procs -> Nat])'
      BY <2>6(*, Zenon*) DEF P
    <3>. QED
      BY <2>6 DEF P, POP, PFunc
  <2>7. ASSUME NEW self \in SubProcs,
               ch(self)
        PROVE  FullTypeOK'
    <3>. (localCh \in POP({0,1}))'
      BY <2>7 DEF ch, SubProcs, POP, PFunc, OtherProcs
    <3>. QED
      BY <2>7 DEF ch
  <2>8. ASSUME NEW self \in SubProcs,
               test(self)
        PROVE  FullTypeOK'
    <3>. (localNum \in POP(Nat \cup {qm}))'
      BY <2>8 DEF test, SubProcs, POP, PFunc, OtherProcs
    <3>. QED
      BY <2>8 DEF test
  <2>9. ASSUME NEW self \in SubProcs,
               Lb(self)
        PROVE  FullTypeOK'
    BY <2>9 DEF Lb, SubProcs, POP, PFunc, OtherProcs
  <2>10. ASSUME NEW self \in SubProcs,
                L2(self)
         PROVE  FullTypeOK'
    BY <2>10 DEF L2
  <2>11. ASSUME NEW self \in SubProcs,
                L3(self)
         PROVE  FullTypeOK'
    BY <2>11 DEF L3
  <2>12. ASSUME NEW self \in WrProcs,
                wrp(self)
         PROVE  FullTypeOK'
    BY <2>12 DEF wrp, wr, WrProcs, POP, PFunc, OtherProcs
  <2>13. CASE UNCHANGED vars
    BY <2>13 DEF vars
  <2>. HIDE DEF FullTypeOK
  <2>14. QED
    BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 
       DEF Next, main, sub
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA TotalOrder ==
  ASSUME FullTypeOK, NEW i \in Procs, NEW j \in OtherProcs(i)
  PROVE  \/ <<number[i], i>> \ll <<number[j], j>>
         \/ <<number[j], j>> \ll <<number[i], i>>
BY DEF \ll, Procs, OtherProcs, FullTypeOK

(***************************************************************************)
(* The following invariant expresses how the main processes and their      *)
(* sub-processes synchronize. This invariant is implicit in the informal   *)
(* presentation where sub-processes appear within the scope of the main    *)
(* processes but must be made explicit in the formal development.          *)
(***************************************************************************)

SyncInv == \A i \in Procs :
  \/ /\ pc[<<i>>] \in {"ncs", "cs", "P"}
     /\ \A j \in OtherProcs(i) : pc[<<i,j>>] = "ch"
  \/ /\ pc[<<i>>] = "M"
     /\ \A j \in OtherProcs(i) : pc[<<i,j>>] \in {"ch", "test"}
  \/ /\ pc[<<i>>] = "M0"
     /\ \A j \in OtherProcs(i) : pc[<<i,j>>] = "test"
  \/ pc[<<i>>] = "L"
  
THEOREM Synchronization == Spec => []SyncInv
<1>1. Init => SyncInv
  BY DisjointIds(*, Zenon*) DEF Init, OtherProcs, ProcSet, ProcIds, SubProcs, SyncInv
<1>2. FullTypeOK /\ SyncInv /\ [Next]_vars => SyncInv'
  <2> SUFFICES ASSUME FullTypeOK,
                      SyncInv,
                      [Next]_vars
               PROVE  SyncInv'
    OBVIOUS
  <2>. USE DEFS FullTypeOK, SyncInv
  \** TODO: Tedious decomposition due to an internal error reported by the SMT backend.
  <2>1. ASSUME NEW self \in Procs, NEW i \in Procs \ {self},
               UNCHANGED pc[<<i>>],
               \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
        PROVE  SyncInv!(i)'
    BY <2>1
  <2>2. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>2 DEF ncs, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>3. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  SyncInv'
    <3>1. /\ pc[<<self>>] = "M"
          /\ \A j \in OtherProcs(self) : pc[<<self,j>>] = "test"
          /\ pc' = [pc EXCEPT ![<<self>>] = "M0"]
      BY <2>3 DEF M, SubProcsOf, SubProcs, OtherProcs
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <3>1 DEF ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>4. ASSUME NEW self \in Procs,
               M0(<<self>>)
        PROVE  SyncInv'
    <3>1. /\ pc[<<self>>] = "M0"
          /\ \A j \in OtherProcs(self) : pc[<<self,j>>] = "test"
          /\ \E l \in {"M0", "L"} : pc' = [pc EXCEPT ![<<self>>] = l]
      BY <2>4 DEF M0
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <3>1 DEF ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>5. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  SyncInv'
    <3>. /\ \A j \in OtherProcs(self) : pc[<<self,j>>] = "ch"
         /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>5 DEF L, ProcIds, SubProcsOf, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>6. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>6 DEF cs, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>7. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>7 DEF P, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>8. ASSUME NEW self \in Procs, NEW oth \in Procs, 
               ch(<<self,oth>>)
        PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>8 DEF ch, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>9. ASSUME NEW self \in Procs, NEW oth \in Procs, 
               test(<<self,oth>>)
        PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>9 DEF test, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>10. ASSUME NEW self \in Procs, NEW oth \in Procs,
                Lb(<<self,oth>>)
         PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>10 DEF Lb, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>11. ASSUME NEW self \in Procs, NEW oth \in Procs,
                L2(<<self,oth>>)
         PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>11 DEF L2, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>12. ASSUME NEW self \in Procs, NEW oth \in Procs,
                L3(<<self,oth>>)
         PROVE  SyncInv'
    <3>. /\ SyncInv!(self)'
         /\ \A i \in Procs \ {self} :
               /\ UNCHANGED pc[<<i>>]
               /\ \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY <2>12 DEF L3, ProcIds, SubProcs, OtherProcs
    <3>. QED
      BY <2>1(*, Zenon*)
  <2>13. ASSUME NEW self \in Procs, NEW oth \in Procs,
                wrp(<<self,oth,"wr">>)
         PROVE  SyncInv'
    <3>. UNCHANGED pc
      BY <2>13 DEF wrp, wr
    <3>. QED
      OBVIOUS (*BY Zenon*)
  <2>14. CASE UNCHANGED vars
    BY <2>14(*, Zenon*) DEF vars
  <2>. HIDE DEFS FullTypeOK, SyncInv
  <2>15. QED
    BY <2>2, <2>11, <2>12, <2>13, <2>14, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10 
       DEF Next, main, sub, ProcIds, SubProcs, WrProcs
<1>. QED  BY <1>1, <1>2, Typing, PTL DEF Spec

(***************************************************************************)
(* The following invariant characterizes the values of localCh, localNum,  *)
(* and number.                                                             *)
(***************************************************************************)

NumInv == \A i \in Procs : 
  /\ number[i] # 0 <=> pc[<<i>>] \in {"L", "cs", "P"}
  /\ \A j \in OtherProcs(i) :
        /\ localCh[j][i] = 1 <=> pc[<<i,j>>] \in {"test", "Lb"}
        /\ localNum[j][i] # number[i] =>
             /\ localNum[j][i] = qm
             /\ \/ pc[<<i>>] = "L" /\ pc[<<i,j>>] = "test"
                \/ pc[<<i>>] \in {"ncs", "M", "M0"}

THEOREM NumberInvariant == Spec => []NumInv
<1>1. Init => NumInv
  <2>1. ASSUME Init, NEW i \in Procs
        PROVE  number[i] = 0 /\ pc[<<i>>] \notin {"L", "cs", "P"}
    BY <2>1(*, Zenon*) DEF Init, ProcSet, ProcIds
  <2>2. ASSUME Init, NEW i \in Procs, NEW j \in OtherProcs(i)
        PROVE  /\ localCh[j][i] # 1 /\ pc[<<i,j>>] \notin {"test", "Lb"}
               /\ localNum[j][i] = number[i]
    BY <2>2, SubProcId(*, Isa*) DEF Init, OtherProcs, ProcSet
  <2>. QED  BY <2>1, <2>2(*, Zenon*) DEF NumInv
<1>2. FullTypeOK /\ SyncInv /\ NumInv /\ [Next]_vars => NumInv'
  <2> SUFFICES ASSUME FullTypeOK,
                      SyncInv,
                      NumInv,
                      [Next]_vars
               PROVE  NumInv'
    OBVIOUS
  <2>. USE DEF FullTypeOK
  <2>1. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self>>] = "ncs"
         /\ pc' = [pc EXCEPT ![<<self>>] = "M"]
         /\ UNCHANGED <<number, localCh, localNum>>
      BY <2>1 DEF ncs
    <3>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY DEF SubProcs, OtherProcs
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv, SubProcs, OtherProcs
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>2. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self>>] = "M"
         /\ pc' = [pc EXCEPT ![<<self>>] = "M0"]
         /\ UNCHANGED <<number, localCh, localNum>>
      BY <2>2 DEF M
    <3>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
      BY DEF SubProcs, OtherProcs
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv, SubProcs, OtherProcs
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>3. ASSUME NEW self \in Procs,
               M0(<<self>>)
        PROVE  NumInv'
    <3>1. CASE unRead[<<self>>] # {}
      <4>. UNCHANGED <<pc, number, localCh, localNum>>
        BY <2>3, <3>1 DEF M0
      <4>. QED  BY (*Isa*) DEF NumInv
    <3>2. CASE unRead[<<self>>] = {}
      <4>. /\ pc[<<self>>] = "M0"
           /\ pc' = [pc EXCEPT ![<<self>>] = "L"]
           /\ \E n \in {m \in Nat : m > v[<<self>>]} : number' = [number EXCEPT ![self] = n]
           /\ localNum' = [j \in Procs |->
                             [i \in OtherProcs(j) |->
                                 IF i = self THEN qm ELSE localNum[j][i]]]
           /\ UNCHANGED localCh
        BY <2>3, <3>2 DEF M0
      <4>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
        BY DEF SubProcs, OtherProcs
      <4>1. ASSUME NEW i \in Procs
            PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
        BY DEF NumInv, ProcIds
      <4>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
            PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
        BY (*Isa*) DEF NumInv
      <4>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                   localNum[j][i]' # number[i]'
            PROVE  /\ localNum[j][i]' = qm
                   /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                      \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
        BY <4>3 DEF NumInv, SyncInv, ProcIds, OtherProcs
      <4>. QED  BY ONLY <4>1, <4>2, <4>3(*, Zenon*) DEF NumInv
    <3>. QED  BY <3>1, <3>2
  <2>4. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self>>] = "L"
         /\ \A j \in OtherProcs(self) : pc[<<self,j>>] = "ch"
         /\ pc' = [pc EXCEPT ![<<self>>] = "cs"]
         /\ UNCHANGED <<number, localNum, localCh>>
      BY <2>4 DEF L, OtherProcs, SubProcsOf, SubProcs
    <3>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
        BY DEF SubProcs, OtherProcs
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>5. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self>>] = "cs"
         /\ pc' = [pc EXCEPT ![<<self>>] = "P"]
         /\ UNCHANGED <<number, localNum, localCh>>
      BY <2>5 DEF cs
    <3>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
        BY DEF SubProcs, OtherProcs
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>6. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self>>] = "P"
         /\ pc' = [pc EXCEPT ![<<self>>] = "ncs"]
         /\ number' = [number EXCEPT ![self] = 0]
         /\ localNum' = [j \in Procs |->
                           [i \in OtherProcs(j) |->
                              IF i = self THEN qm ELSE localNum[j][i]]]
         /\ UNCHANGED localCh
      BY <2>6 DEF P
    <3>. \A i \in Procs : \A j \in OtherProcs(i) : UNCHANGED pc[<<i,j>>]
        BY DEF SubProcs, OtherProcs
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds, OtherProcs
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>7. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               ch(<<self,oth>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self,oth>>] = "ch"
         /\ pc[<<self>>] = "M"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "test"]
         /\ localCh' = [localCh EXCEPT ![oth][self] = 1]
         /\ UNCHANGED <<number, localNum>>
      BY <2>7 DEF ch
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      <4>1. CASE i = self /\ j = oth
        BY <3>2, <4>1 DEF NumInv, OtherProcs, SubProcs, POP, PFunc
      <4>2. CASE ~(i = self /\ j = oth)
        <5>. UNCHANGED <<localCh[j][i], pc[<<i,j>>]>>
          BY <3>2, <4>2 DEF SubProcs, OtherProcs, POP, PFunc
        <5>. QED  BY (*Isa*) DEF NumInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds, SubProcs, OtherProcs
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>8. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               test(<<self,oth>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self,oth>>] = "test"
         /\ pc[<<self>>] = "L"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "Lb"]
         /\ localNum' = [localNum EXCEPT ![oth][self] = number[self]]
         /\ UNCHANGED <<number, localCh>>
      BY <2>8 DEF test
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      <4>1. CASE i = self /\ j = oth
        BY <3>2, <4>1 DEF NumInv, OtherProcs, SubProcs
      <4>2. CASE ~(i = self /\ j = oth)
        <5>. UNCHANGED <<localNum[j][i], pc[<<i,j>>]>>
          BY <3>2, <4>2 DEF SubProcs, OtherProcs, POP, PFunc
        <5>. QED  BY (*Isa*) DEF NumInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      <4>1. CASE i = self /\ j = oth
        BY <3>3, <4>1 DEF NumInv, OtherProcs, SubProcs, POP, PFunc
      <4>2. CASE ~(i = self /\ j = oth)
        BY <3>3, <4>2 DEF NumInv, ProcIds, SubProcs, OtherProcs, POP, PFunc
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>9. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               Lb(<<self,oth>>)
        PROVE  NumInv'
    <3>. /\ pc[<<self,oth>>] = "Lb"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L2"]
         /\ localCh' = [localCh EXCEPT ![oth][self] = 0]
         /\ UNCHANGED <<number, localNum>>
      BY <2>9 DEF Lb
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      <4>1. CASE i = self /\ j = oth
        BY <3>2, <4>1 DEF NumInv, OtherProcs, SubProcs, POP, PFunc
      <4>2. CASE ~(i = self /\ j = oth)
        <5>. UNCHANGED <<localCh[j][i], pc[<<i,j>>]>>
          BY <3>2, <4>2 DEF SubProcs, OtherProcs, POP, PFunc
        <5>. QED  BY (*Isa*) DEF NumInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds, SubProcs, OtherProcs, POP, PFunc
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>10. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                L2(<<self,oth>>)
         PROVE  NumInv'
    <3>. /\ pc[<<self,oth>>] = "L2"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L3"]
         /\ UNCHANGED <<number, localNum, localCh>>
      BY <2>10 DEF L2
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      <4>1. CASE i = self /\ j = oth
        BY <3>2, <4>1(*, Isa*) DEF NumInv, OtherProcs, SubProcs
      <4>2. CASE ~(i = self /\ j = oth)
        <5>. UNCHANGED pc[<<i,j>>]
          BY <3>2, <4>2 DEF SubProcs, OtherProcs
        <5>. QED  BY (*Isa*) DEF NumInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds, SubProcs, OtherProcs
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>11. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                L3(<<self,oth>>)
         PROVE  NumInv'
    <3>. /\ pc[<<self,oth>>] = "L3"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "ch"]
         /\ UNCHANGED <<number, localNum, localCh>>
      BY <2>11 DEF L3
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv, ProcIds
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      <4>1. CASE i = self /\ j = oth
        BY <3>2, <4>1(*, Isa*) DEF NumInv, OtherProcs, SubProcs
      <4>2. CASE ~(i = self /\ j = oth)
        <5>. UNCHANGED pc[<<i,j>>]
          BY <3>2, <4>2 DEF SubProcs, OtherProcs
        <5>. QED  BY (*Isa*) DEF NumInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, ProcIds, SubProcs, OtherProcs, POP, PFunc
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>12. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                wrp(<<self,oth,"wr">>)
         PROVE  NumInv'
    <3>. /\ pc[<<self>>] \in {"ncs", "M", "M0"}
         /\ localNum' = [localNum EXCEPT ![oth][self] = 0]
         /\ UNCHANGED <<pc, number, localCh>>
      BY <2>12 DEF wrp, wr
    <3>1. ASSUME NEW i \in Procs
          PROVE  number[i]' # 0 <=> pc[<<i>>]' \in {"L", "cs", "P"}
      BY DEF NumInv
    <3>2. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  localCh[j][i]' = 1 <=> pc[<<i,j>>]' \in {"test", "Lb"}
      BY (*Isa*) DEF NumInv
    <3>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
                 localNum[j][i]' # number[i]'
          PROVE  /\ localNum[j][i]' = qm
                 /\ \/ pc[<<i>>]' = "L" /\ pc[<<i,j>>]' = "test"
                    \/ pc[<<i>>]' \in {"ncs", "M", "M0"}
      BY <3>3 DEF NumInv, OtherProcs, POP, PFunc
    <3>. QED  BY ONLY <3>1, <3>2, <3>3(*, Zenon*) DEF NumInv
  <2>13. CASE UNCHANGED vars
    BY <2>13(*, Isa*) DEF vars, NumInv
  <2>14. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
       DEF Next, main, sub, ProcIds, SubProcs, WrProcs, OtherProcs
<1>. QED  BY <1>1, <1>2, Typing, Synchronization, PTL DEF Spec 

(***************************************************************************)
(* The following properties are stated in the explanations of the various  *)
(* predicates.                                                             *)
(***************************************************************************)
LEMMA inBakeryNum ==
  ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
         inBakery(i,j), FullTypeOK, SyncInv, NumInv
  PROVE  /\ number[i] \in Nat \ {0}
         /\ localNum[j][i] = number[i]
BY DEF inBakery, FullTypeOK, SyncInv, NumInv

LEMMA passedInBakery ==
  ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), NEW LL
  PROVE  /\ passed(i,j,LL) => inBakery(i,j)
         /\ passed(i,j,LL)' => inBakery(i,j)'
BY DEF passed, inBakery

(***************************************************************************)
(* We now prove the main invariant of the algorithm.                       *)
(***************************************************************************)

THEOREM Invariance == Spec => []I
<1>1. Init => I
  BY (*Zenon*)
  DEF Init, I, OtherProcs, Inv, inBakery, passed, 
      ProcSet, ProcIds, SubProcs, WrProcs
<1>2. FullTypeOK /\ SyncInv /\ NumInv /\ I /\ [Next]_vars => I'
  <2> SUFFICES ASSUME FullTypeOK, SyncInv, NumInv,
                      I,
                      [Next]_vars
               PROVE  I'
    OBVIOUS
  <2>. USE DEF FullTypeOK
  <2>1. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  I'
    <3>. USE <2>1 DEF ncs
    <3>1. \A i \in Procs : \A j \in OtherProcs(i) : inBakery(i,j)' <=> inBakery(i,j)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. \A i \in Procs : \A j \in OtherProcs(i) : \A w \in Nat : inDoorwayVal(i,j,w)' <=> inDoorwayVal(i,j,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>3. \A i \in Procs : \A j \in OtherProcs(i) : inDoorway(i,j)' <=> inDoorway(i,j)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>4. \A i \in Procs : \A j \in OtherProcs(i) : 
             /\ passed(i,j,"L2")' <=> passed(i,j,"L2")
             /\ passed(i,j,"L3")' <=> passed(i,j,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>5. \A i \in Procs : \A j \in OtherProcs(i) : Before(i,j)' <=> Before(i,j)
      BY <3>1, <3>2, <3>3, <3>4 DEF Before, Outside, OtherProcs
    <3>. QED
      BY <3>1, <3>3, <3>4, <3>5 DEF I, Inv, OtherProcs
  <2>2. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  I'
    <3>. USE <2>2 DEF M
    <3>1. \A i \in Procs : \A j \in OtherProcs(i) : inBakery(i,j)' <=> inBakery(i,j)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. \A i \in Procs : \A j \in OtherProcs(i) : \A w \in Nat :
             inDoorwayVal(i,j,w)' <=> inDoorwayVal(i,j,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>3. \A i \in Procs : \A j \in OtherProcs(i) :
             inDoorway(i,j)' <=> inDoorway(i,j)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>4. \A i \in Procs : \A j \in OtherProcs(i) : 
             /\ passed(i,j,"L2")' <=> passed(i,j,"L2")
             /\ passed(i,j,"L3")' <=> passed(i,j,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>5. \A i \in Procs : \A j \in OtherProcs(i) : Before(i,j)' <=> Before(i,j)
      BY <3>1, <3>2, <3>3, <3>4 DEF Before, Outside, OtherProcs
    <3>. QED
      BY <3>1, <3>3, <3>4, <3>5 DEF I, Inv, OtherProcs
  <2>3. ASSUME NEW self \in Procs,
               M0(<<self>>)
        PROVE  I'
    <3>1. CASE unRead[<<self>>] # {}
      <4>. PICK j \in unRead[<<self>>] :
                /\ pc[<<self>>] = "M0"
                /\ IF localNum[self][j] # qm
                   THEN v' = [v EXCEPT ![<<self>>] = Max(v[<<self>>], localNum[self][j])]
                   ELSE v' = v
                /\ unRead' = [unRead EXCEPT ![<<self>>] = unRead[<<self>>] \ {j}]
                /\ UNCHANGED << pc, number >>
        BY <2>3, <3>1 DEF M0
      <4>. /\ j \in Procs
           /\ j \in OtherProcs(self)
           /\ self \in OtherProcs(j)
        BY DEF ProcIds, OtherProcs
      <4>1. \A p,q \in Procs : inBakery(p,q)' <=> inBakery(p,q)
        BY DEF inBakery
      <4>2. \A p \in Procs : \A q \in OtherProcs(p) :
               inDoorway(p,q)' <=> \/ self = p /\ q = j
                                   \/ inDoorway(p,q)
        BY DEF inDoorway, OtherProcs, ProcIds
      <4>3. ASSUME localNum[self][j] # qm 
            PROVE  inDoorwayVal(self,j,number[j])'
        <5>1. v'[<<self>>] >= localNum[self][j]
          BY <4>3 DEF ProcIds, POP, PFunc, Max
        <5>2. NumInv!(j)!2!(self)
          BY DEF NumInv
        <5>. QED  BY <4>3, <5>1, <5>2 DEF inDoorwayVal, ProcIds
      <4>4. \A p,q \in Procs : 
               /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
               /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
        BY DEF passed
      <4>5. ASSUME NEW p \in Procs \ {self}, NEW q \in OtherProcs(p),
                   q # self \/ p # j
            PROVE  Before(q,p)' <=> Before(q,p)
        <5>. Outside(p,q)' <=> Outside(p,q)
          BY <4>1, <4>2, <4>5 DEF Outside, OtherProcs
        <5>. UNCHANGED v[<<p>>]
          BY <4>5 DEF ProcIds, OtherProcs
        <5>. QED  BY <4>1, <4>4, <4>5 DEF Before, inDoorwayVal, ProcIds, OtherProcs
      (* For the converse relation we only have an implication. *)
      <4>6. ASSUME NEW p \in Procs \ {self}, NEW q \in OtherProcs(p),
                   q # self \/ p # j
            PROVE  Before(p,q) => Before(p,q)'
        <5>1. Outside(q,p)' <=> Outside(q,p)
          BY <4>1, <4>2, <4>6 DEF Outside, OtherProcs
        <5>2. inDoorwayVal(q,p,number[p]) => inDoorwayVal(q,p,number[p])'
          <6>. p \in unRead'[<<q>>] <=> p \in unRead[<<q>>]
            BY <4>6 DEF ProcIds, OtherProcs
          <6>. v[<<q>>] >= number[p] => v[<<q>>]' >= number'[p]
            <7>1. CASE q = self
              BY <7>1 DEF ProcIds, OtherProcs, Max, POP, PFunc
            <7>2. CASE q # self
              BY <7>2 DEF ProcIds, OtherProcs
            <7>. QED  BY <4>6, <7>1, <7>2
          <6>. QED  BY DEF inDoorwayVal
        <5>. QED  BY <4>1, <4>4, <5>1, <5>2 DEF Before, OtherProcs
      <4>7. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), inBakery(p,q)
            PROVE  Before(p,q)' \/ Before(q,p)' \/ inDoorway(q,p)'
        <5>1. CASE p = self  \* ~ inBakery(p,q)
          BY <4>7, <5>1 DEF inBakery, SyncInv
        <5>2. CASE q = self /\ p = j  \* inDoorway(self,j)'
          BY <4>2, <5>2 DEF OtherProcs
        <5>3. CASE p # self /\ (q # self \/ p # j)
          BY <4>2, <4>5, <4>6, <4>7, <5>3 DEF I, Inv, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>8. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), passed(p,q,"L2")
            PROVE  Before(p,q)' \/ Before(q,p)'
        <5>1. CASE p = self  \* ~ passed(self,q,"L2")
          BY <4>8, <5>1 DEF passed, SyncInv
        <5>2. CASE q = self /\ p = j
          <6>1. inBakery(j,self)
            BY <4>8, <5>2 DEF passed, inBakery
          <6>2. localNum[self][j] # qm
            BY <6>1, inBakeryNum, qmNotNat DEF POP, PFunc
          <6>. QED  BY <4>1, <4>3, <5>2, <6>1, <6>2 DEF Before
        <5>3. CASE p # self /\ (q # self \/ p # j)
          BY <4>5, <4>6, <4>8, <5>3 DEF I, Inv, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>9. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), passed(p,q,"L3")
            PROVE  Before(p,q)'
        <5>1. CASE p = self  \* ~ passed(self,q,"L3")
          BY <4>9, <5>1 DEF passed, SyncInv
        <5>2. CASE q = self /\ p = j
          <6>1. inBakery(j,self)
            BY <4>9, <5>2 DEF passed, inBakery
          <6>2. localNum[self][j] # qm
            BY <6>1, inBakeryNum, qmNotNat DEF POP, PFunc
          <6>. QED  BY <4>1, <4>3, <5>2, <6>1, <6>2 DEF Before
        <5>3. CASE p # self /\ (q # self \/ p # j)
          BY <4>5, <4>6, <4>9, <5>3 DEF I, Inv, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>. QED  BY <4>1, <4>4, <4>7, <4>8, <4>9 DEF OtherProcs, I, Inv
    <3>2. CASE unRead[<<self>>] = {}
      <4>. PICK n \in Nat :
                /\ pc[<<self>>] = "M0"
                /\ n > v[<<self>>]
                /\ number' = [number EXCEPT ![self] = n]
                /\ localNum' = [j \in Procs |->
                                      [i \in OtherProcs(j) |->
                                             IF i = self THEN qm
                                                         ELSE localNum[j][i]]]
                /\ v' = [v EXCEPT ![<<self>>] = 0]
                /\ pc' = [pc EXCEPT ![<<self>>] = "L"]
                /\ UNCHANGED unRead
        BY <2>3, <3>2 DEF M0
      <4>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
            PROVE  inBakery(p,q)' <=> inBakery(p,q)
        BY DEF inBakery, SyncInv, ProcIds, SubProcs, OtherProcs
      <4>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
            PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
        BY <3>2 DEF inDoorway, SyncInv, ProcIds, SubProcs, OtherProcs
      <4>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
            PROVE  inDoorwayVal(p,q,w) => inDoorwayVal(p,q,w)'
        \* Here we only have an implication since for p = self we
        \* cannot conclude v[<<self>>] >= w from number'[self] >= w.
        BY <3>2 DEF inDoorwayVal, SyncInv, ProcIds, SubProcs, OtherProcs
      <4>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
            PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                   /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
        BY DEF passed, SyncInv, ProcIds, SubProcs, OtherProcs
      <4>5. \A p \in OtherProcs(self) : ~ inBakery(self,p)
        BY DEF inBakery, SyncInv
      <4>6. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
            PROVE  Before(p,q) => Before(p,q)'
        BY <4>1, <4>2, <4>3, <4>4, <4>5(*, Zenon*) DEF Before, Outside, OtherProcs
      <4>. QED  BY <4>1, <4>2, <4>4, <4>6 DEF I, Inv, OtherProcs
    <3>. QED  BY <3>1, <3>2
  <2>4. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  I'
    <3>. /\ pc[<<self>>] = "L"
         /\ \A p \in SubProcsOf(self) : pc[p] = "ch"
         /\ pc' = [pc EXCEPT ![<<self>>] = "cs"]
         /\ UNCHANGED << number, unRead, v >>
      BY <2>4 DEF L
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcsOf, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcsOf, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, SubProcsOf, SubProcs, OtherProcs, ProcIds
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4 DEF I, Inv, Before, Outside, OtherProcs
  <2>5. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  I'
    <3>. /\ pc[<<self>>] = "cs"
         /\ pc' = [pc EXCEPT ![<<self>>] = "P"]
         /\ UNCHANGED << number, unRead, v >>
      BY <2>5 DEF cs
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q) /\ p # self
      BY DEF inBakery, SyncInv, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs \ {self}, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>5. \A q \in OtherProcs(self) :
             /\ passed(self,q,"L2") /\ ~ passed(self,q,"L2")'
             /\ passed(self,q,"L3") /\ ~ passed(self,q,"L3")'
      BY DEF passed, SyncInv, ProcIds, SubProcs, OtherProcs
    <3>6. ASSUME NEW p \in Procs \ {self}, NEW q \in OtherProcs(p) \ {self}
          PROVE  Before(p,q) => Before(p,q)'
      BY <3>1, <3>2, <3>3, <3>4 DEF Before, Outside, OtherProcs
    <3>7. \A q \in OtherProcs(self) : inBakery(q,self)' => Before(q, self)'
      BY <3>1 DEF Before, Outside, inDoorway  \* have Outside(self,q)'
    <3>. QED  
      BY passedInBakery, <3>1, <3>2, <3>4, <3>5, <3>6, <3>7 DEF OtherProcs, I, Inv
  <2>6. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  I'
    <3>. /\ pc[<<self>>] = "P"
         /\ number' = [number EXCEPT ![self] = 0]
         /\ pc' = [pc EXCEPT ![<<self>>] = "ncs"]
         /\ UNCHANGED << unRead, v >>
      BY <2>6 DEF P
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>5. \A q \in OtherProcs(self) : ~ inBakery(self,q)
      BY DEF inBakery, SyncInv
    <3>9. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  Before(p,q) => Before(p,q)'
      <4>1. CASE q = self  \* follows from Outside(self,p)'
        BY <3>1, <3>2, <3>5, <3>9, <4>1 DEF Before, inDoorway, Outside, OtherProcs
      <4>2. CASE q # self
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>9, <4>2 DEF Before, OtherProcs, Outside
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>1, <3>2, <3>4, <3>9 DEF I, Inv, OtherProcs
  <2>7. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               ch(<<self,oth>>)
        PROVE  I'
    <3>. /\ pc[<<self,oth>>] = "ch"
         /\ pc[<<self>>] = "M"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "test"]
         /\ UNCHANGED <<number, unRead, v>>
      BY <2>7 DEF ch
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4 DEF I, Inv, Before, OtherProcs, Outside
  <2>8. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               test(<<self,oth>>)
        PROVE  I'
    <3>. /\ pc[<<self,oth>>] = "test"
         /\ pc[<<self>>] = "L"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "Lb"]
         /\ UNCHANGED <<number, unRead, v>>
      BY <2>8 DEF test
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q) \/ (p = self /\ q = oth)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q) /\ ~(p = self /\ q = oth)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w) /\ ~(p = self /\ q = oth)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>5. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), Before(p,q)
          PROVE  Before(p,q)'
      <4>1. CASE p = oth /\ q = self
        <5>1. inBakery(oth, self)' /\ inBakery(self,oth)'
          BY <3>5, <3>1, <4>1 DEF Before, OtherProcs
        <5>2. inDoorway(self,oth) /\ ~ inBakery(self,oth)
          BY DEF inDoorway, inBakery
        <5>3. inDoorwayVal(self, oth, number[oth])
          BY <3>5, <4>1, <5>2 DEF Before, Outside
        <5>4. <<number[oth], oth>> \ll <<number[self], self>>
          BY <5>3 DEF inDoorwayVal, \ll, OtherProcs
        <5>. QED  BY <4>1, <5>1, <5>4 DEF Before, passed
      <4>2. CASE p # oth \/ q # self
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <4>2 DEF Before, Outside, OtherProcs
      <4>. QED  BY <4>1, <4>2
    <3>6. ASSUME inBakery(oth, self)
          PROVE  Before(self, oth)' \/ Before(oth, self)'
      <4>1. inBakery(self, oth)' /\ inBakery(oth, self)'
        BY <3>6, <3>1 DEF OtherProcs
      <4>2. ~ passed(self, oth, "L3")'
        BY DEF passed
      <4>3. CASE passed(oth, self, "L3")  \* Before(oth, self), hence Before(oth, self)'
        BY <4>3, <3>5 DEF I, Inv, OtherProcs
      <4>4. CASE ~ passed(oth, self, "L3")  \* Before(self,oth)' \/ Before(oth,self)'
        BY <4>1, <4>2, <4>4, <3>4, TotalOrder DEF Before, OtherProcs
      <4>. QED  BY <4>3, <4>4
    <3>7. Before(self, oth)' \/ Before(oth, self)' \/ inDoorway(oth, self)'
      <4>1. CASE Outside(oth, self)  \* inBakery(self,oth)' /\ Outside(oth,self)'
        BY <4>1, <3>1, <3>2 DEF Before, Outside, OtherProcs
      <4>2. CASE inDoorway(oth, self)  \* inDoorway(oth, self)'
        BY <4>2, <3>2 DEF OtherProcs
      <4>3. CASE inBakery(oth, self)
        BY <4>3, <3>6
      <4>. QED  BY <4>1, <4>2, <4>3 DEF Outside
    <3>. QED  BY <3>1, <3>2, <3>4, <3>5, <3>6, <3>7 DEF I, Inv, OtherProcs
  <2>9. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               Lb(<<self,oth>>)
        PROVE  I'
    <3>. /\ pc[<<self,oth>>] = "Lb"
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L2"]
         /\ UNCHANGED <<number, unRead, v>>
      BY <2>9 DEF Lb
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4 DEF I, Inv, Before, Outside, OtherProcs
  <2>10. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                L2(<<self,oth>>)
         PROVE  I'
    <3>. /\ pc[<<self,oth>>] = "L2"
         /\ localCh[self][oth] = 0
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L3"]
         /\ UNCHANGED <<number, unRead, v>>
      BY <2>10 DEF L2
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ~ inDoorway(oth,self)
      BY DEF inDoorway, NumInv, SyncInv, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>5. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2") \/ (p = self /\ q = oth)
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY DEF passed, ProcIds, SubProcs, OtherProcs
    <3>6. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  Before(p,q)' <=> Before(p,q)
      BY <3>1, <3>2, <3>4, <3>5 DEF Before, Outside, OtherProcs
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>5, <3>6, passedInBakery DEF I, Inv, OtherProcs
  <2>11. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                L3(<<self,oth>>)
         PROVE  I'
    <3>. /\ pc[<<self,oth>>] = "L3"
         /\ \/ localNum[self][oth] \in {0,qm}
            \/ <<number[self], self>> \ll <<localNum[self][oth], oth>>
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "ch"]
         /\ UNCHANGED <<number, unRead, v>>
      BY <2>11 DEF L3
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY DEF inBakery, SyncInv, ProcIds, SubProcs, OtherProcs
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY DEF inDoorway, ProcIds, SubProcs, OtherProcs
    <3>3. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY DEF inDoorwayVal, ProcIds, SubProcs, OtherProcs
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  passed(p,q,"L2")' <=> passed(p,q,"L2")
      <4>1. CASE p = self /\ q = oth
        BY <4>1 DEF passed, SyncInv, ProcIds, SubProcs, OtherProcs
      <4>2. CASE p # self \/ q # oth
        BY <4>2 DEF passed, ProcIds, SubProcs, OtherProcs
      <4>. QED  BY <4>1, <4>2
    <3>5. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  passed(p,q,"L3")' <=> passed(p,q,"L3") \/ (p = self /\ q = oth)
      BY DEF passed, SyncInv, ProcIds, SubProcs, OtherProcs
    <3>6. passed(self, oth, "L2")
      BY DEF passed
    <3>7. ASSUME Before(oth, self)  PROVE FALSE
      <4>1. inBakery(oth, self)
        BY <3>7 DEF Before
      <4>2. ~ Outside(self, oth)
        BY DEF Outside, inBakery
      <4>3. ~ inDoorwayVal(self, oth, number[oth])
        BY DEF inDoorwayVal, SyncInv
      <4>4. <<number[oth], oth>> \ll <<number[self], self>>
        BY <3>7, <4>2, <4>3 DEF Before
      <4>5. /\ number[oth] = localNum[self][oth]
            /\ number[oth] \in Nat \ {0}
        BY inBakeryNum, <4>1(*, Zenon*) DEF OtherProcs
      <4>6. <<number[self], self>> \ll <<number[oth], oth>>
        BY <4>5, qmNotNat
      <4>. QED  BY <4>6, <4>4 DEF \ll, Procs, OtherProcs
    <3>8. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), q # self \/ p # oth
          PROVE  Before(p,q)' <=> Before(p,q)
      BY <3>1, <3>2, <3>3, <3>5, <3>8 DEF Before, Outside, OtherProcs
    <3>. QED  BY <3>1, <3>2, <3>4, <3>5, <3>6, <3>7, <3>8 DEF I, Inv, OtherProcs
  <2>X. CASE UNCHANGED <<pc, number, unRead, v>>
    <3>1. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inBakery(p,q)' <=> inBakery(p,q)
      BY <2>X DEF inBakery
    <3>2. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  inDoorway(p,q)' <=> inDoorway(p,q)
      BY <2>X DEF inDoorway
    <3>4. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p), NEW w \in Nat
          PROVE  inDoorwayVal(p,q,w)' <=> inDoorwayVal(p,q,w)
      BY <2>X DEF inDoorwayVal
    <3>5. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  /\ passed(p,q,"L2")' <=> passed(p,q,"L2")
                 /\ passed(p,q,"L3")' <=> passed(p,q,"L3")
      BY <2>X DEF passed
    <3>6. ASSUME NEW p \in Procs, NEW q \in OtherProcs(p)
          PROVE  Before(p,q)' <=> Before(p,q)
      BY <2>X, <3>1, <3>2, <3>4, <3>5 DEF Before, Outside, OtherProcs
    <3>. QED
      BY <3>1, <3>2, <3>5, <3>6 DEF I, Inv, OtherProcs
  <2>12. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                wr(<<self, oth, "wr">>)
         PROVE  I'
    BY <2>12, <2>X DEF wr
  <2>13. CASE UNCHANGED vars
    BY <2>13, <2>X DEF vars
  <2>14. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
       DEF Next, main, sub, ProcIds, SubProcs, WrProcs, wrp, OtherProcs
<1>. QED  BY <1>1, <1>2, Typing, Synchronization, NumberInvariant, PTL DEF Spec

(***************************************************************************)
(* It follows that the algorithm guarantees mutual exclusion.              *)
(***************************************************************************)
THEOREM Spec => []MutualExclusion
<1>1. FullTypeOK /\ SyncInv /\ I => MutualExclusion
  <2>. SUFFICES ASSUME FullTypeOK, SyncInv, I,
                       NEW p \in Procs, NEW q \in Procs, q # p,
                       pc[<<p>>] = "cs", pc[<<q>>] = "cs"
                PROVE  FALSE
    BY DEF MutualExclusion, ProcIds
  <2>1. passed(p,q,"L3") /\ passed(q,p,"L3")
    BY DEF passed, SyncInv, OtherProcs
  <2>2. Before(p,q) /\ Before(q,p)
    BY <2>1 DEF I, Inv, OtherProcs
  <2>3. ~ Outside(p,q) /\ ~ Outside(q,p)
    BY DEF Outside, inBakery, SyncInv, OtherProcs
  <2>4. ~ inDoorwayVal(p,q,number[q]) /\ ~ inDoorwayVal(q,p,number[p])
    BY DEF inDoorwayVal
  <2>5. /\ <<number[p], p>> \ll <<number[q], q>>
        /\ <<number[q], q>> \ll <<number[p], p>>
    BY <2>2, <2>3, <2>4 DEF Before
  <2>. QED  BY <2>5 DEF \ll, Procs, FullTypeOK
<1>. QED  BY <1>1, Typing, Synchronization, Invariance, PTL

=============================================================================
\* Modification History
\* Last modified Tue Dec 07 15:01:23 CET 2021 by adefourn
\* Last modified Wed Aug 25 17:03:48 CEST 2021 by merz
\* Created Thu Jul 01 12:26:36 CEST 2021 by merz
