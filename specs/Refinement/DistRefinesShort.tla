---------------------------- MODULE DistRefinesShort ----------------------------
(***************************************************************************)
(* We use TLAPS to prove that the distributed Bakery algorithm refines the *)
(* deconstructed Bakery algorithm (with atomic choice of ticket numbers).  *)
(***************************************************************************)
EXTENDS BakeryDistributed, SequenceTheorems

LEMMA ackNotNat == ack \notin Nat \cup {qm}
BY NoSetContainsEverything DEF ack

(***************************************************************************)
(* The following lemma should be included in SequenceTheorems.             *)
(***************************************************************************)
LEMMA RangeHeadTail ==
  ASSUME NEW S, NEW s \in Seq(S) \ {<< >>}
  PROVE  Range(s) = {Head(s)} \cup Range(Tail(s))
  BY HeadTailProperties, RangeEquality DEF Range
(*<1>1. ASSUME NEW x \in Range(s), x # Head(s)
      PROVE  x \in Range(Tail(s))
  <2>1. PICK i \in 2 .. Len(s) : s[i] = x
    BY <1>1 DEF Range
  <2>2. /\ Tail(s) \in Seq(S)
        /\ i-1 \in 1 .. Len(Tail(s))
        /\ Tail(s)[i-1] = x
    BY <2>1, HeadTailProperties
  <2>. QED  BY <2>2, RangeEquality(*, Zenon*)
<1>. QED  BY <1>1 DEF Range
*)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following is a full type invariant for the algorithm.               *)
(***************************************************************************)
FullTypeOK ==
  /\ number \in [Procs -> Nat]
  /\ localNum \in POP(Nat)
  /\ localCh \in POP({0,1})
  /\ ackRcvd \in POP({0,1})
  /\ q \in POP(Seq(Nat \cup {ack}))
  /\ pc \in [ProcSet -> {"ncs", "M", "L", "cs", "P", "ch", "L0", "L2", "L3", "wr"}]
  /\ \A p \in ProcIds : pc[p] \in {"ncs", "M", "L", "cs", "P"}
  /\ \A p \in SubProcs : pc[p] \in {"ch", "L0", "L2", "L3"}
  /\ \A p \in MsgProcs : pc[p] = "wr"

THEOREM Typing == Spec => []FullTypeOK
<1>1. Init => FullTypeOK
  BY DisjointIds DEF Init, FullTypeOK, ProcSet, OtherProcs, POP, PFunc
(*  <2>. SUFFICES ASSUME Init PROVE FullTypeOK
    OBVIOUS
  <2>. << >> \in Seq(Nat \cup {ack})
    OBVIOUS
  <2>. /\ localNum \in POP(Nat)
       /\ localCh \in POP({0,1})
       /\ ackRcvd \in POP({0,1})
       /\ q \in POP(Seq(Nat \cup {ack}))
    BY POP_construct, Isa DEF Init
  <2>. QED  BY DisjointIds DEF Init, FullTypeOK, ProcSet
*)
<1>2. FullTypeOK /\ [Next]_vars => FullTypeOK'
  <2> SUFFICES ASSUME FullTypeOK,
                      [Next]_vars
               PROVE  FullTypeOK'
    \*OBVIOUS
  <2>. USE DEF FullTypeOK, OtherProcs
  <2>1. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  FullTypeOK'
    \*BY <2>1 DEF ncs, ProcSet, ProcIds
  <2>2. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  FullTypeOK'
(*    <3>. PICK v \in Nat :
              /\ number' = [number EXCEPT ![self] = v]
              /\ q' = [q EXCEPT ![self] = 
                         [j \in OtherProcs(self) |-> Append(q[self][j], v)]]
              /\ pc' = [pc EXCEPT ![<<self>>] = "L"]
              /\ UNCHANGED <<localNum, localCh, ackRcvd>>
      BY <2>2(*, Isa*) DEF M
    <3>1. \A j \in OtherProcs(self) : Append(q[self][j], v) \in Seq(Nat \cup {ack})
      BY POP_access
    <3>2. q' \in POP(Seq(Nat \cup {ack}))
      BY <3>1, POP_except_fun_type, Isa
    <3>. QED  BY <3>2 DEF ProcSet, ProcIds
*)
  <2>3. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  FullTypeOK'
    \*BY <2>3 DEF L, ProcSet, ProcIds
  <2>4. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  FullTypeOK'
    \*BY <2>4 DEF cs, ProcSet, ProcIds
  <2>5. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  FullTypeOK'
    <3>. /\ ackRcvd' = [ackRcvd EXCEPT ![self] = [j \in OtherProcs(self) |-> 0]]
         /\ number' = [number EXCEPT ![self] = 0]
         /\ q' = [q EXCEPT ![self] = [j \in OtherProcs(self)
                                           |-> Append(q[self][j],0)]]
         /\ pc' = [pc EXCEPT ![<<self>>] = "ncs"]
         /\ UNCHANGED << localNum, localCh >>
      \*BY <2>5 DEF P
    <3>1. ackRcvd' \in POP({0,1})
\*      BY POP_except_fun_type, Isa   -- why doesn't this work here?
      BY DEF POP, PFunc, OtherProcs
(*      <4>. DEFINE g(i,j) == 0
      <4>1. /\ ackRcvd \in POP({0,1})
            /\ ackRcvd' = [ackRcvd EXCEPT ![self] = [j \in OtherProcs(self) |-> g(self,j)]]
        OBVIOUS
      <4>2. \A j \in OtherProcs(self) : g(self,j) \in {0,1}
        OBVIOUS
      <4>. HIDE DEF g
      <4>. QED  BY ONLY <4>1, <4>2, POP_except_fun_type, Isa
*)
    <3>2. \A j \in OtherProcs(self) : Append(q[self][j], 0) \in Seq(Nat \cup {ack})
      \*BY POP_access
    <3>3. q' \in POP(Seq(Nat \cup {ack}))
      \*BY <3>2, POP_except_fun_type, Isa
    <3>. QED  \*BY <3>1, <3>3(*, Zenon*) DEF ProcSet, ProcIds
  <2>6. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               ch(<<self,oth>>)
        PROVE  FullTypeOK'
    \*BY <2>6, POP_except(*, Zenon*) DEF ch, ProcSet, SubProcs
  <2>7. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L0(<<self,oth>>)
        PROVE  FullTypeOK'
    \*BY <2>7, POP_except(*, Zenon*) DEF L0, ProcSet, SubProcs
  <2>8. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L2(<<self,oth>>)
        PROVE  FullTypeOK'
    \*BY <2>8 DEF L2, ProcSet, SubProcs
  <2>9. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L3(<<self,oth>>)
        PROVE  FullTypeOK'
    \*BY <2>9 DEF L3, ProcSet, SubProcs  
  <2>10. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                msg(<<self,oth,"msg">>)
         PROVE  FullTypeOK'
    <3>. /\ q[oth][self] # << >>
         /\ LET v == Head(q[oth][self])
            IN  /\ IF v = ack
                   THEN /\ ackRcvd' = [ackRcvd EXCEPT ![self][oth] = 1]
                        /\ UNCHANGED localNum
                   ELSE /\ localNum' = [localNum EXCEPT ![self][oth] = v]
                        /\ UNCHANGED ackRcvd
                /\ IF v \in {0, ack}
                   THEN q' = [q EXCEPT ![oth][self] = Tail(@)]
                   ELSE q' = [q EXCEPT ![oth][self] = Tail(@),
                                       ![self][oth] = Append(@, ack)]
         /\ UNCHANGED << number, localCh, pc >>
      \*BY <2>10 DEF msg, wr
    <3>. DEFINE v == Head(q[oth][self])
    <3>0. v \in Nat \cup {ack}
      \*BY POP_access
    <3>1. localNum' \in POP(Nat)
      \*BY <3>0, POP_except(*, Isa*)
    <3>2. ackRcvd' \in POP({0,1})
      \*BY POP_except(*, Isa*)
    <3>3. q' \in POP(Seq(Nat \cup {ack}))
      BY POP_access, POP_except
(*      <4>. DEFINE q1 == [q EXCEPT ![oth][self] = Tail(@)]
                  q2 == [q1 EXCEPT ![self][oth] = Append(@, ack)]
      <4>0. Tail(q[oth][self]) \in Seq(Nat \cup {ack})
        BY POP_access
      <4>1. q1 \in POP(Seq(Nat \cup {ack}))
        BY <4>0, POP_except(*, Isa*)
      <4>. HIDE DEF q1
      <4>a. Append(q1[self][oth], ack) \in Seq(Nat \cup {ack})
        BY <4>1, POP_access
      <4>2. q2 \in POP(Seq(Nat \cup {ack}))
        BY <4>1, <4>a, POP_except(*, Isa*)
      <4>. QED  BY <4>1, <4>2(*, Zenon*) DEF q1
*)
    <3>. QED  \*BY <3>1, <3>2, <3>3
  <2>11. CASE UNCHANGED vars
    \*BY <2>11 DEF vars
  <2>. HIDE DEF FullTypeOK
  <2>12. QED
    \*BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
    \*   DEF Next, main, sub, ProcIds, SubProcs, MsgProcs
<1>. QED  \*BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following inductive invariant relates the contents of the           *)
(* communication channels and of the local variables. It is instrumental   *)
(* for the refinement proof below.                                         *)
(***************************************************************************)

Inv == 
  /\ \A i \in Procs : number[i] # 0 <=> pc[<<i>>] \in {"L", "cs", "P"}
  /\ \A i \in Procs : number[i] = 0 => 
        \A j \in OtherProcs(i) : ackRcvd[i][j] = 0 /\ ack \notin Range(q[j][i])
  /\ \A i \in Procs : \A j \in OtherProcs(i) : number[i] # 0 =>
     (***********************************************************************)
     (* The following describes a state machine of how ticket numbers are   *)
     (* propagated to subprocesses and how acknowledgements are received.   *)
     (***********************************************************************)
        \/ /\ pc[<<i,j>>] = "L0"
           /\ pc[<<i>>] = "L"
           /\ number[i] \in Range(q[i][j])
           /\ ack \notin Range(q[j][i])
           /\ ackRcvd[i][j] = 0
        \/ /\ pc[<<i,j>>] = "L0"
           /\ pc[<<i>>] = "L"
           /\ number[i] \notin Range(q[i][j])
           /\ 0 \notin Range(q[i][j])
           /\ ack \in Range(q[j][i])
           /\ ackRcvd[i][j] = 0
           /\ localNum[j][i] = number[i]
        \/ /\ number[i] \notin Range(q[i][j])
           /\ 0 \notin Range(q[i][j])
           /\ ack \notin Range(q[j][i])
           /\ ackRcvd[i][j] = 1
           /\ localNum[j][i] = number[i]
  /\ \A i \in Procs : \A j \in OtherProcs(i) : \A k,l \in 1 .. Len(q[i][j]) :
     (***********************************************************************)
     (* Facts about the contents of communication channels.                 *)
     (***********************************************************************)
        \* no message appears more than once
        /\ q[i][j][k] = q[i][j][l] => k = l
        \* non-zero messages correspond to the current ticket of the sender
        /\ q[i][j][k] \in Nat \ {0} => q[i][j][k] = number[i]
        \* zeros precede ticket numbers
        /\ q[i][j][k] = 0 /\ q[i][j][l] \in Nat \ {0} => k < l

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
  BY DEF Inv, Init, ProcSet, ProcIds, SubProcs, MsgProcs, OtherProcs, Range
(*  <2>1. ASSUME Init, NEW i \in Procs
        PROVE  /\ number[i] = 0
               /\ pc[<<i>>] \notin {"L", "cs", "P"}
    BY <2>1(*, Zenon*) DEF Init, ProcSet, ProcIds, SubProcs, MsgProcs
  <2>2. ASSUME Init, NEW i \in Procs, NEW j \in OtherProcs(i)
        PROVE  ackRcvd[i][j] = 0 /\ ack \notin Range(q[j][i])
    BY <2>2 DEF Init, Range, OtherProcs
  <2>3. ASSUME Init, NEW i \in Procs, NEW j \in OtherProcs(i),
                NEW k \in 1 .. Len(q[i][j]), NEW l \in 1 .. Len(q[i][j])
        PROVE  FALSE
    BY <2>3 DEF Init
  <2>. QED  BY <2>1, <2>2, <2>3(*, Zenon*) DEF Inv
*)
<1>2. FullTypeOK /\ Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME FullTypeOK,
                      Inv,
                      [Next]_vars
               PROVE  Inv'
    \*OBVIOUS
  <2>. USE DEF FullTypeOK
  <2>1. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  Inv'
    \*BY <2>1 DEF ncs, Inv, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>2. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  Inv'
    <3>. /\ pc[<<self>>] = "M"
         /\ \A oth \in Procs \ {self} : pc[<<self,oth>>] = "L0"
         /\ pc' = [pc EXCEPT ![<<self>>] = "L"]
         /\ UNCHANGED <<localNum, ackRcvd>>
      \*BY <2>2 DEF M, SubProcsOf, SubProcs
    <3>. PICK v \in Nat \ {0} :
              /\ number' = [number EXCEPT ![self] = v]
              /\ q' = [q EXCEPT ![self] = [j \in OtherProcs(self) |-> Append(q[self][j], v)]]
      \*BY <2>2(*, Isa*) DEF M
    <3>1. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  /\ q[i][j] \in Seq(Nat \cup {ack})
                 /\ q'[i][j] = IF i = self THEN Append(q[self][j], v) ELSE q[i][j]
      \*BY DEF OtherProcs, POP, PFunc
    <3>2. Inv!1'
      BY DEF FullTypeOK, Inv, ProcSet, ProcIds
(*      <4>1. Inv!1
        BY (*Zenon*) DEF Inv
      <4>. QED
        BY <4>1(*, Zenon*) DEF FullTypeOK, ProcSet, ProcIds
*)
    <3>3. ASSUME NEW i \in Procs, number'[i] = 0, NEW j \in OtherProcs(i)
          PROVE  ackRcvd'[i][j] = 0 /\ ack \notin Range(q'[j][i])
      BY <3>1, <3>3, ackNotNat, AppendProperties DEF Inv, Range, OtherProcs
(*      <4>1. ackRcvd'[i][j] = 0
        BY <3>3 DEF Inv
      <4>2. ack \notin Range(q[j][i])
        BY <3>3 DEF Inv
      <4>3. ack \notin Range(q'[j][i])
        BY ONLY <4>2, <3>1, ackNotNat, AppendProperties DEF Range, OtherProcs
      <4>. QED  BY <4>1, <4>3
*)
    <3>4. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), number'[i] # 0
          PROVE  Inv!3!(i)!(j)!2'
      BY <3>1, <3>4, AppendProperties, ackNotNat DEF Inv, ProcSet, ProcIds, SubProcs, OtherProcs, Range
(*      <4>1. CASE i = self
        <5>1. pc'[<<i,j>>] = "L0"
          BY <4>1 DEF ProcSet, SubProcs, OtherProcs
        <5>2. pc'[<<i>>] = "L"
          BY <4>1 DEF ProcSet, ProcIds
        <5>3. v \in Range(q'[i][j])
          BY ONLY <3>1, <4>1, AppendProperties DEF Range
        <5>4. /\ ackRcvd[i][j] = 0
              /\ ack \notin Range(q[j][i])
          BY <4>1 DEF Inv
        <5>5. ack \notin Range(q'[j][i])
          BY <3>1, <4>1, <5>4 DEF OtherProcs
        <5>. QED  BY <4>1, <5>1, <5>2, <5>3, <5>4, <5>5
      <4>2. CASE i # self
        <5>1. Inv!3!(i)!(j)!2
          BY <3>4, <4>2 DEF Inv
        <5>2. UNCHANGED << number[i], pc[<<i>>], pc[<<i,j>>], q[i][j] >>
          BY <4>2, <3>1 DEF ProcSet, ProcIds, SubProcs, OtherProcs
        <5>3. ack \in Range(q'[j][i]) <=> ack \in Range(q[j][i])
          BY ONLY <3>1, ackNotNat, AppendProperties DEF Range, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>. QED  BY <4>1, <4>2
*)
    <3>5. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i),
                 NEW k \in 1 .. Len(q'[i][j]), NEW l \in 1 .. Len(q'[i][j])
          PROVE  Inv!4!(i)!(j)!(k,l)'
      BY <3>1, ackNotNat DEF Inv
(*      <4>1. CASE i = self
        <5>. ASSUME NEW kk \in 1 .. Len(q[self][j])
              PROVE  q[self][j][kk] \in {0, ack}
          <6>1. number[self] = 0
            BY DEF Inv
          <6>2. q[self][j][kk] \in Nat \cup {ack}
            BY ONLY <3>1, <4>1
          <6>3. q[self][j][kk] \in Nat \ {0} => q[self][j][kk] = number[self]
            BY <3>1, <4>1 DEF Inv
          <6>. QED  BY <6>1, <6>2, <6>3
        <5>. QED  BY <3>1, <4>1, ackNotNat DEF Inv
      <4>2. CASE i # self
        BY <3>1, <4>2 DEF Inv
      <4>. QED  BY <4>1, <4>2
*)
    <3>. QED  BY ONLY <3>2, <3>3, <3>4, <3>5 DEF Inv
  <2>3. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  Inv'
    \*BY <2>3 DEF L, FullTypeOK, Inv, ProcSet, ProcIds, SubProcsOf, SubProcs, OtherProcs
  <2>4. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  Inv'
    \*BY <2>4 DEF cs, FullTypeOK, Inv, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>5. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  Inv'
    <3>. /\ pc[<<self>>] = "P"
         /\ ackRcvd' = [ackRcvd EXCEPT ![self] = [j \in OtherProcs(self) |-> 0]]
         /\ number' = [number EXCEPT ![self] = 0]
         /\ q' = [q EXCEPT ![self] = [j \in OtherProcs(self) |-> Append(q[self][j], 0)]]
         /\ pc' = [pc EXCEPT ![<<self>>] = "ncs"]
         /\ UNCHANGED localNum
      \*BY <2>5 DEF P
    <3>1. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
          PROVE  /\ ackRcvd'[i][j] = IF i = self THEN 0 ELSE ackRcvd[i][j]
                 /\ q[i][j] \in Seq(Nat \cup {ack})
                 /\ q'[i][j] = IF i = self THEN Append(q[i][j], 0) ELSE q[i][j]
      \*BY DEF FullTypeOK, POP, PFunc
    <3>2. ASSUME NEW i \in Procs
          PROVE  number'[i] # 0 <=> pc'[<<i>>] \in {"L", "cs", "P"}
      \*BY DEF FullTypeOK, Inv, ProcSet, ProcIds
    <3>3. ASSUME NEW i \in Procs, number'[i] = 0, NEW j \in OtherProcs(i)
          PROVE  ackRcvd'[i][j] = 0 /\ ack \notin Range(q'[j][i])
      BY <3>1, <3>3, AppendProperties, ackNotNat DEF Inv, Range, OtherProcs
(*      <4>1. CASE i = self
        <5>. ack \notin Range(q[j][i])
          BY <4>1(*, Zenon*) DEF Inv
        <5>. QED  BY <3>1, <4>1(*, Isa*) DEF OtherProcs
      <4>2. CASE j = self
        <5>1. ackRcvd[i][j] = 0 /\ ack \notin Range(q[j][i])
          BY <3>3, <4>2 DEF Inv, OtherProcs
        <5>. QED  BY ONLY <3>1, <4>2, <5>1, AppendProperties, ackNotNat DEF Range, OtherProcs
      <4>3. CASE i # self /\ j # self
        BY <3>1, <3>3, <4>3 DEF Inv, Range, OtherProcs
      <4>. QED  BY <4>1, <4>2, <4>3
*)
    <3>4. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), number'[i] # 0
          PROVE  Inv!3!(i)!(j)!2'
      BY <3>1, <3>4, AppendProperties, ackNotNat DEF Inv, ProcSet, ProcIds, SubProcs, OtherProcs, Range
(*      <4>1. Inv!3!(i)!(j)!2
        BY <3>4 DEF Inv
      <4>2. UNCHANGED << pc[<<i>>], pc[<<i,j>>], number[i], q[i][j], ackRcvd[i][j] >>
        BY <3>1, <3>4 DEF ProcSet, ProcIds, SubProcs, OtherProcs
      <4>3. ack \in Range(q'[j][i]) <=> ack \in Range(q[j][i])
        BY ONLY <3>1, <3>4, AppendProperties, ackNotNat DEF Range, OtherProcs
      <4>. QED  BY <4>1, <4>2, <4>3
*)
    <3>5. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i),
                 NEW k \in 1 .. Len(q'[i][j]), NEW l \in 1 .. Len(q'[i][j])
          PROVE  Inv!4!(i)!(j)!(k,l)'
      BY <3>1, Inv, RangeEquality, ackNotNat DEF Inv
(*      <4>1. CASE i = self
        <5>1. /\ number[self] \notin Range(q[self][j])
              /\ 0 \notin Range(q[self][j])
          BY <4>1(*, Zenon*) DEF Inv
        <5>2. ASSUME NEW n \in 1 .. Len(q[self][j])
              PROVE  q[self][j][n] = ack
          BY ONLY <3>1, <4>1, <5>1, Inv, RangeEquality DEF Inv
        <5>. QED  BY <3>1, <4>1, <5>2, ackNotNat DEF Inv
      <4>2. CASE i # self
        BY <3>1, <4>2 DEF Inv
      <4>. QED  BY <4>1, <4>2
*)
    <3>. QED  \*BY <3>2, <3>3, <3>4, <3>5(*, Zenon*) DEF Inv
  <2>6. ASSUME NEW self \in Procs, NEW oth \in Procs \ {self},
               ch(<<self,oth>>)
        PROVE  Inv'
    \*BY <2>6 DEF FullTypeOK, Inv, ch, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>7. ASSUME NEW self \in Procs, NEW oth \in Procs \ {self},
               L0(<<self,oth>>)
        PROVE  Inv'
    \*BY <2>7 DEF FullTypeOK, Inv, L0, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>8. ASSUME NEW self \in Procs, NEW oth \in Procs \ {self},
               L2(<<self,oth>>)
        PROVE  Inv'
    \*BY <2>8 DEF FullTypeOK, Inv, L2, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>9. ASSUME NEW self \in Procs, NEW oth \in Procs \ {self},
               L3(<<self,oth>>)
        PROVE  Inv'
    \*BY <2>9 DEF FullTypeOK, Inv, L3, ProcSet, ProcIds, SubProcs, OtherProcs
  <2>10. ASSUME NEW self \in Procs, NEW oth \in Procs \ {self},
                msg(<<self,oth,"msg">>)
         PROVE  Inv'
    <3>. DEFINE v == Head(q[oth][self])
    <3>. /\ q[oth][self] # << >>
         /\ IF v = ack
            THEN /\ ackRcvd' = [ackRcvd EXCEPT ![self][oth] = 1]
                 /\ localNum' = localNum
            ELSE /\ localNum' = [localNum EXCEPT ![self][oth] = v]
                 /\ ackRcvd' = ackRcvd
         /\ UNCHANGED <<pc, number>>
      \*BY <2>10 DEF msg, wr
    <3>q. IF v \in {0,ack}
          THEN q' = [q EXCEPT ![oth][self] = Tail(@)]
          ELSE q' = [q EXCEPT ![oth][self] = Tail(@),
                              ![self][oth] = Append(q[self][oth], ack)]
      \*BY <2>10 DEF msg, wr
    <3>1. Inv!1'
      \*BY DEF Inv
    <3>2. CASE v = ack
      BY <3>2, <3>q, POP_access, POP_except, ackNotNat, RangeHeadTail
      DEF Inv, FullTypeOK, POP, PFunc, Range, ProcSet, ProcIds, SubProcs, OtherProcs
(*      <4>. ack \in Range(q[oth][self])
        BY <3>2 DEF FullTypeOK, POP, PFunc, OtherProcs, Range
      <4>. /\ ackRcvd' = [ackRcvd EXCEPT ![self][oth] = 1]
           /\ localNum' = localNum
           /\ q' = [q EXCEPT ![oth][self] = Tail(@)]
           /\ q[oth][self] \in Seq(Nat \cup {ack})
           /\ Tail(q[oth][self]) \in Seq(Nat \cup {ack})
        BY <3>2, <3>q, POP_access DEF OtherProcs
      <4>1. q'[oth][self] = Tail(q[oth][self])
        BY POP_except(*, Isa*) DEF OtherProcs
      <4>2. ASSUME NEW i \in Procs, number[i] = 0, NEW j \in OtherProcs(i)
            PROVE  /\ ackRcvd'[i][j] = 0 
                   /\ ack \notin Range(q'[j][i])
        <5>1. /\ ackRcvd[i][j] = 0
              /\ ack \notin Range(q[j][i])
          BY <4>2 DEF Inv
        <5>2. ackRcvd'[i][j] = ackRcvd[i][j]
          BY <5>1, POP_except DEF OtherProcs
        <5>3. q'[j][i] = q[j][i]
          BY <5>1, POP_except DEF OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), number[i] # 0
            PROVE  Inv!3!(i)!(j)!2'
        <5>1. CASE i = self /\ j = oth
          <6>1. /\ number[self] \notin Range(q[self][oth])
                /\ 0 \notin Range(q[self][oth])
                /\ localNum[oth][self] = number[self]
            BY <4>3, <5>1(*, Zenon*) DEF Inv
          <6>2. ackRcvd'[self][oth] = 1
            BY POP_except(*, Isa*) DEF OtherProcs
          <6>3. q'[self][oth] = q[self][oth]
            BY POP_except DEF OtherProcs
          <6>4. ASSUME ack \in Range(Tail(q[oth][self]))
                PROVE  FALSE
            <7>1. PICK k \in 1 .. Len(Tail(q[oth][self])) : Tail(q[oth][self])[k] = ack
              BY <6>4 DEF Range
            <7>2. /\ k+1 \in 1 .. Len(q[oth][self])
                  /\ q[oth][self][k+1] = ack
                  /\ q[oth][self][1] = ack
              BY <3>2, <7>1
            <7>. QED  BY <7>2 DEF Inv, OtherProcs
          <6>. QED  BY <5>1, <6>1, <6>2, <6>3, <4>1, <6>4
        <5>2. CASE i = oth /\ j = self
          <6>1. UNCHANGED << ackRcvd[oth][self], q[self][oth] >>
            BY POP_except DEF OtherProcs
          <6>2. ASSUME NEW n \in Nat
                PROVE  n \in Range(q[oth][self]) <=> n \in Range(Tail(q[oth][self]))
            BY <3>2, ackNotNat, RangeHeadTail
          <6>. QED  BY <4>3, <5>2, <6>1, <4>1, <6>2 DEF Inv, OtherProcs
        <5>3. CASE /\ ~(i = self /\ j = oth)
                   /\ ~(i = oth /\ j = self)
          BY <4>3, <5>3, POP_except DEF Inv, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>4. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i),
                   NEW k \in 1 .. Len(q'[i][j]), NEW l \in 1 .. Len(q'[i][j])
            PROVE  Inv!4!(i)!(j)!(k,l)'
        <5>0. Inv!4!(i)!(j)
          BY DEF Inv
        <5>1. CASE i = oth /\ j = self
          <6>. /\ k \in 1 .. Len(Tail(q[oth][self]))
               /\ l \in 1 .. Len(Tail(q[oth][self]))
            BY <4>1, <5>1(*, Zenon*)
          <6>. /\ k+1 \in 1 .. Len(q[oth][self])
               /\ l+1 \in 1 .. Len(q[oth][self])
               /\ Tail(q[oth][self])[k] = q[oth][self][k+1]
               /\ Tail(q[oth][self])[l] = q[oth][self][l+1]
            OBVIOUS
          <6>. QED  BY <4>1, <5>0, <5>1
        <5>2. CASE ~(i = oth /\ j = self)
          BY <5>0, <5>2, POP_except DEF OtherProcs
        <5>. QED  BY <5>1, <5>2
      <4>. QED  BY <4>2, <4>3, <4>4 DEF Inv  \* Inv!1' is trivially preserved
*)
    <3>3. CASE v = 0
      BY <3>3, <3>q, POP_except, POP_access, ackNotNat, RangeHeadTail
      DEF Inv, FullTypeOK, Range, POP, PFunc, OtherProcs
(*      <4>. 0 \in Range(q[oth][self])
        BY <3>3 DEF FullTypeOK, POP, PFunc, OtherProcs, Range
      <4>. /\ ackRcvd' = ackRcvd
           /\ localNum' = [localNum EXCEPT ![self][oth] = 0]
           /\ q' = [q EXCEPT ![oth][self] = Tail(@)]
           /\ q[oth][self] \in Seq(Nat \cup {ack})
           /\ Tail(q[oth][self]) \in Seq(Nat \cup {ack})
        BY <3>3, <3>q, POP_access, ackNotNat DEF OtherProcs
      <4>1. q'[oth][self] = Tail(q[oth][self])
        BY POP_except(*, Isa*) DEF OtherProcs
      <4>2. ASSUME NEW i \in Procs, number[i] = 0, NEW j \in OtherProcs(i)
            PROVE  ackRcvd'[i][j] = 0 /\ ack \notin Range(q'[j][i])
        <5>1. ackRcvd[i][j] = 0 /\ ack \notin Range(q[j][i])
          BY <4>2 DEF Inv
        <5>2. CASE i = self /\ j = oth
          BY <4>1, <5>1, <5>2 DEF Range
        <5>3. CASE ~(i = self /\ j = oth)
          BY <5>1, <5>3, POP_except DEF OtherProcs
        <5>. QED  BY <5>2, <5>3
      <4>3. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), number[i] # 0
            PROVE  Inv!3!(i)!(j)!2'
        <5>1. CASE i = self /\ j = oth
          <6>1. UNCHANGED << q[self][oth], localNum[oth][self] >>
            BY POP_except DEF OtherProcs
          <6>2. ack \in Range(q'[oth][self]) <=> ack \in Range(q[oth][self])
            BY <3>3, <4>1, ackNotNat, RangeHeadTail
          <6>. QED  BY <4>3, <5>1, <6>1, <6>2 DEF Inv
        <5>2. CASE i = oth /\ j = self
          <6>1. UNCHANGED q[self][oth]
            BY POP_except DEF OtherProcs
          <6>2. number[i] \in Range(q'[oth][self]) <=> number[i] \in Range(q[oth][self])
            BY <3>3, <4>1, <4>3, RangeHeadTail
          <6>. QED  BY <4>3, <5>2, <6>1, <6>2 DEF Inv
        <5>3. CASE /\ ~(i = self /\ j = oth)
                   /\ ~(i = oth /\ j = self)
          BY <4>3, <5>3, POP_except DEF Inv, OtherProcs
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>4. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i),
                   NEW k \in 1 .. Len(q'[i][j]), NEW l \in 1 .. Len(q'[i][j])
            PROVE  Inv!4!(i)!(j)!(k,l)'
        BY <4>1, POP_except DEF Inv, OtherProcs
        <5>0. Inv!4!(i)!(j)
          BY DEF Inv
        <5>1. CASE i = oth /\ j = self
          <6>. /\ k \in 1 .. Len(Tail(q[oth][self]))
               /\ l \in 1 .. Len(Tail(q[oth][self]))
            BY <4>1, <5>1(*, Zenon*)
          <6>. /\ k+1 \in 1 .. Len(q[oth][self])
               /\ l+1 \in 1 .. Len(q[oth][self])
               /\ Tail(q[oth][self])[k] = q[oth][self][k+1]
               /\ Tail(q[oth][self])[l] = q[oth][self][l+1]
            OBVIOUS
          <6>. QED  BY <4>1, <5>0, <5>1
        <5>2. CASE ~(i = oth /\ j = self)
          BY <5>0, <5>2, POP_except DEF OtherProcs
        <5>. QED  BY <5>1, <5>2
      <4>. QED  BY <4>2, <4>3, <4>4 DEF Inv
*)
    <3>4. CASE v \in Nat \ {0}
      \* FIXME not merging further for now, too difficult for SMT
      \*BY <3>1, <3>4, <3>q, POP_access, POP_except,
      \*     ackNotNat, RangeEquality, AppendProperties
      \*DEF Inv, FullTypeOK, POP, PFunc, Range, OtherProcs
      <4>0. Len(q[oth][self]) \in Int
        \*OBVIOUS
      <4>a. v = number[oth]
        \*BY <3>4, POP_access DEF Inv, OtherProcs
      <4>b. number[oth] \in Range(q[oth][self])
        \*BY <4>a DEF FullTypeOK, POP, PFunc, OtherProcs, Range
      <4>. /\ ackRcvd' = ackRcvd
           /\ localNum' = [localNum EXCEPT ![self][oth] = v]
           /\ q' = [q EXCEPT ![oth][self] = Tail(@),
                             ![self][oth] = Append(q[self][oth], ack)]
           /\ q[oth][self] \in Seq(Nat \cup {ack})
           /\ Tail(q[oth][self]) \in Seq(Nat \cup {ack})
           /\ q[self][oth] \in Seq(Nat \cup {ack})
           /\ Append(q[self][oth], ack) \in Seq(Nat \cup {ack})
        \*BY <3>4, <3>q, POP_access, ackNotNat DEF OtherProcs
      <4>d. ASSUME 0 \in Range(q[oth][self])
            PROVE  FALSE
        BY <3>4, <4>d, RangeEquality DEF Inv, OtherProcs
(*        <5>. PICK k \in 1 .. Len(q[oth][self]) : q[oth][self][k] = 0
          BY <4>d, RangeEquality
        <5>. QED  BY <3>4 DEF Inv, OtherProcs
*)
      <4>1. /\ q' \in POP(Seq(Nat \cup {ack}))
            /\ q'[oth][self] = Tail(q[oth][self])
            /\ q'[self][oth] = Append(q[self][oth], ack)
            /\ \A i \in Procs : \A j \in Procs \ {i} :
                  ~(i = self /\ j = oth) /\ ~(i = oth /\ j = self)
               => q'[i][j] = q[i][j]
        BY POP_except DEF OtherProcs
(*        <5>. DEFINE tl == Tail(q[oth][self])
                    qq == [q EXCEPT ![oth][self] = tl]
        <5>. tl \in Seq(Nat \cup {ack})
          OBVIOUS  \* needed because we will hide the definition of tl
        <5>1. q' = [qq EXCEPT ![self][oth] = Append(q[self][oth], ack)]
          OBVIOUS
        <5>. HIDE DEF tl
        <5>2. /\ qq \in POP(Seq(Nat \cup {ack}))
              /\ qq[oth][self] = tl
          BY POP_except(*, Isa*) DEF OtherProcs
        <5>3. \A i \in Procs : \A j \in OtherProcs(i) :
                 i # oth \/ j # self => qq[i][j] = q[i][j]
          BY POP_except DEF OtherProcs
        <5>. HIDE DEF qq
        <5>4. /\ q' \in POP(Seq(Nat \cup {ack}))
              /\ q'[self][oth] = Append(q[self][oth], ack)
              /\ \A i \in Procs : \A j \in OtherProcs(i) :
                    i # self \/ j # oth => q'[i][j] = qq[i][j]
          BY ONLY <5>1, <5>2, Append(q[self][oth], ack) \in Seq(Nat \cup {ack}), 
                  POP_except(*, Isa*) DEF OtherProcs
        <5>. QED  BY ONLY <5>2, <5>3, <5>4 DEF OtherProcs, tl
*)
      <4>5. ASSUME NEW i \in Procs, number'[i] = 0, NEW j \in OtherProcs(i)
            PROVE  ackRcvd'[i][j] = 0 /\ ack \notin Range(q'[j][i])
        BY <3>4, <4>a, <4>1, <4>5 DEF Inv, Range, OtherProcs
(*        <5>1. ackRcvd'[i][j] = 0 /\ ack \notin Range(q[j][i])
          BY <4>5 DEF Inv
        <5>2. i # oth
          BY <3>4, <4>a, <4>5
        <5>3. CASE i = self /\ j = oth
          <6>. Range(Tail(q[oth][self])) \subseteq Range(q[oth][self])
            BY DEF Range
          <6>. QED  BY <4>1, <5>1, <5>3(*, Zenon*)
        <5>4. CASE i # self \/ j # oth
          BY ONLY <4>1, <5>1, <5>2, <5>4 DEF OtherProcs
        <5>. QED  BY <5>3, <5>4
*)
      <4>6. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), number'[i] # 0
            PROVE  Inv!3!(i)!(j)!2'
        BY <3>4, <4>a, <4>b, <4>d, <4>1,
           POP_except, RangeHeadTail, AppendProperties, ackNotNat
        DEF Inv, Range, OtherProcs
(*        <5>1. Inv!3!(i)!(j)!2
          BY <4>6 DEF Inv
        <5>2. CASE i = self /\ j = oth
          <6>1. \A n \in Nat : n \in Range(q[self][oth]) <=> n \in Range(q'[self][oth])
            BY ONLY q[self][oth] \in Seq(Nat \cup {ack}), <4>1, ackNotNat, AppendProperties DEF Range
          <6>2. ack \in Range(q[oth][self]) <=> ack \in Range(q'[oth][self])
            BY <3>4, <4>1, ackNotNat, RangeHeadTail
          <6>3. UNCHANGED localNum[oth][self]
            BY <3>4, POP_except DEF OtherProcs
          <6>. QED  BY <5>1, <5>2, <6>1, <6>2, <6>3(*, Zenon*)
        <5>3. CASE i = oth /\ j = self
          <6>1. /\ pc[<<oth,self>>] = "L0"
                /\ pc[<<oth>>] = "L"
                /\ ackRcvd[oth][self] = 0
            BY <5>1, <5>3, <4>b
          <6>2. /\ number[oth] \notin Range(q'[oth][self])
                /\ 0 \notin Range(q'[oth][self])
            <7>. ASSUME v \in Range(Tail(q[oth][self]))
                 PROVE  FALSE
              <8>1. PICK k \in 1 .. Len(Tail(q[oth][self])) : Tail(q[oth][self])[k] = v
                BY DEF Range
              <8>2. k+1 \in 1 .. Len(q[oth][self]) /\ q[oth][self][k+1] = v
                BY <8>1
              <8>. QED  BY <8>2 DEF Inv, OtherProcs
            <7>. QED  BY <4>a, <4>d, <4>1, RangeHeadTail
          <6>3. ack \in Range(q'[self][oth])
            BY <4>1, AppendProperties(*, Isa*) DEF Range
          <6>4. localNum'[self][oth] = number[oth]
            BY <4>a, POP_except(*, Isa*) DEF OtherProcs
          <6>. QED  BY <5>3, <6>1, <6>2, <6>3, <6>4
        <5>4. CASE ~(i = self /\ j = oth) /\ ~(i = oth /\ j = self)
          <6>. UNCHANGED <<q[i][j], q[j][i]>>
            BY ONLY <4>1, <5>4 DEF OtherProcs
          <6>. QED  BY <3>4, <5>1, <5>4, POP_except DEF OtherProcs
        <5>. QED  BY <5>2, <5>3, <5>4
*)
      <4>7. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i),
                   NEW k \in 1 .. Len(q'[i][j]), NEW l \in 1 .. Len(q'[i][j])
            PROVE  Inv!4!(i)!(j)!(k,l)'
        BY <3>4, <4>1, <4>a, <4>b, ackNotNat, POP_access
        DEF Inv, Range, OtherProcs
(*        <5>0. Inv!4!(i)!(j)
          BY DEF Inv
        <5>1. CASE i = self /\ j = oth
          <6>1. \A n \in 1 .. Len(q'[self][oth]) : 
                   q'[self][oth][n] \in Nat => /\ n \in 1 .. Len(q[self][oth])
                                               /\ q[self][oth][n] = q'[self][oth][n]
            BY ONLY q[self][oth] \in Seq(Nat \cup {ack}), <4>1, ackNotNat
          <6>2. ASSUME NEW n \in 1 .. Len(q'[self][oth]), q'[self][oth][n] = ack
                PROVE  n = Len(q'[self][oth])
            <7>1. ack \notin Range(q[self][oth])
              BY <3>4, <4>a, <4>b(*, Zenon*) DEF Inv, OtherProcs
            <7>. QED  BY ONLY q[self][oth] \in Seq(Nat \cup {ack}), <4>1, <6>2, <7>1 DEF Range
          <6>3. Len(q'[self][oth]) = Len(q[self][oth])+1
            BY <4>1
          <6>4. ASSUME q'[self][oth][k] = q'[self][oth][l]
                PROVE  k = l
            <7>1. CASE q'[self][oth][k] \in Nat
              BY ONLY <5>0, <5>1, <6>1, <6>4, <7>1
            <7>2. CASE q'[self][oth][k] = ack
              BY ONLY <5>1, <6>2, <6>4, <7>2(*, Zenon*)
            <7>. QED  BY ONLY <7>1, <7>2, <4>1, <5>1, POP_access DEF OtherProcs
          <6>5. ASSUME q'[self][oth][k] \in Nat \ {0}
                PROVE  q'[self][oth][k] = number[self]
            BY ONLY <5>0, <5>1, <6>1, <6>5
          <6>6. ASSUME q'[self][oth][k] = 0, q'[self][oth][l] \in Nat \ {0}
                PROVE  k < l
            BY ONLY <5>0, <5>1, <6>1, <6>6
          <6>. QED  BY <5>1, <6>4, <6>5, <6>6
        <5>2. CASE i = oth /\ j = self
          <6>1. q'[oth][self] = Tail(q[oth][self])
            BY <4>1
          <6>2. /\ k+1 \in 1 .. Len(q[oth][self]) /\ q'[oth][self][k] = q[oth][self][k+1]
                /\ l+1 \in 1 .. Len(q[oth][self]) /\ q'[oth][self][l] = q[oth][self][l+1]
            BY ONLY q[oth][self] \in Seq(Nat \cup {ack}) \ {<<>>}, <5>2, <6>1
          <6>. QED  BY <5>0, <5>2, <6>2
        <5>3. CASE ~(i = self /\ j = oth) /\ ~(i = oth /\ j = self)
          <6>. q'[i][j] = q[i][j]
            BY ONLY <4>1, <5>3 DEF OtherProcs
          <6>. QED  BY <5>0(*, Zenon*)
        <5>. QED  BY <5>1, <5>2, <5>3(*, Zenon*)
*)
      <4>. QED  BY ONLY <3>1, <4>5, <4>6, <4>7 DEF Inv
    <3>. QED  \*BY <3>2, <3>3, <3>4 DEF FullTypeOK, POP, PFunc, OtherProcs
  <2>11. CASE UNCHANGED vars
    \*BY <2>11 DEF Inv, vars
  <2>12. QED
    \*BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
    \*   DEF Next, ProcIds, SubProcs, MsgProcs, main, sub
<1>. QED  \*BY <1>1, <1>2, Typing, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following operators define the refinement mapping.                  *)
(***************************************************************************)

DecLN ==  \* value to substitute for localNumber
  [i \in Procs |-> [j \in OtherProcs(i) |->
     IF number[j] \in Range(q[j][i]) THEN qm 
     ELSE localNum[i][j]
  ]]

DecProcSet == ProcIds \cup SubProcs \cup WrProcs

DecPC ==  \* PC value of the deconstructed Bakery algorithm
  [self \in DecProcSet |->
      IF self \in ProcIds THEN pc[self]
      ELSE IF self \in SubProcs
      THEN IF pc[self] = "L0"
           THEN IF pc[<<self[1]>>] = "L" /\ DecLN[self[2]][self[1]] = number[self[1]]
                THEN "Lb" ELSE "test"
           ELSE pc[self]
      ELSE "wr"]

LEMMA DecLN_type == 
  FullTypeOK => DecLN \in POP(Nat \cup {qm})
  BY POP_access DEF FullTypeOK, POP, PFunc, OtherProcs, DecLN
(*<1>. DEFINE s(i,j) == IF number[j] \in Range(q[j][i]) THEN qm 
                      ELSE localNum[i][j]
<1>. FullTypeOK => \A i \in Procs : \A j \in OtherProcs(i) : s(i,j) \in Nat \cup {qm}
  BY POP_access DEF FullTypeOK, OtherProcs
<1>. QED  BY POP_construct, Isa DEF DecLN
*)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Instantiation of the high-level spec for the refinement mapping.        *)
(***************************************************************************)
Dec == INSTANCE BakeryDeconstructedAtomic
       WITH localNum <- DecLN, pc <- DecPC

DecSafety == Dec!Init /\ [][Dec!Next]_(Dec!vars)

LEMMA DecEqualities ==
  /\ Dec!Procs = Procs
  /\ Dec!ProcSet = DecProcSet
  /\ Dec!ProcIds = ProcIds
  /\ Dec!SubProcs = SubProcs
  /\ Dec!WrProcs = WrProcs
  /\ \A p : Dec!SubProcsOf(p) = SubProcsOf(p)
  /\ \A p : Dec!OtherProcs(p) = OtherProcs(p)
  /\ \A x,y : Dec!\ll(x,y) = \ll(x,y)
  /\ \A x,y : Dec!Max(x,y) = Max(x,y)
  /\ Dec!qm = qm
(*BY DEF Dec!Procs, Procs, Dec!ProcSet, DecProcSet, Dec!ProcIds, Dec!SubProcs,
       Dec!WrProcs, ProcIds, SubProcs, WrProcs, Dec!SubProcsOf, SubProcsOf,
       Dec!OtherProcs, OtherProcs, Dec!\ll, \ll, Dec!Max, Max, Dec!qm, qm*)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of refinement (safety part).                                      *)
(***************************************************************************)

THEOREM Refinement == Spec => DecSafety
<1>1. Init => Dec!Init
  BY DisjointIds, DecEqualities
  DEF Init, ProcSet, DecPC, DecLN, DecProcSet, Range, OtherProcs, Dec!Int
(*  <2>. SUFFICES ASSUME Init PROVE Dec!Init
    OBVIOUS
  <2>1. number = [i \in Procs |-> 0]
    BY DEF Init
  <2>2. DecLN = [i \in Procs |-> [j \in OtherProcs(i) |-> 0]]
    BY DEF Init, DecLN, Range, OtherProcs
  <2>3. localCh = [i \in Procs |-> [j \in OtherProcs(i) |-> 0]]
    BY DEF Init
  <2>4. DecPC = [self \in DecProcSet |-> CASE self \in ProcIds -> "ncs"
                                         [] self \in SubProcs -> "ch"
                                         [] self \in WrProcs -> "wr"]
    BY DisjointIds DEF Init, ProcSet, DecPC, DecProcSet
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, DecEqualities DEF Dec!Init, DecProcSet
*)
<1>2. /\ FullTypeOK /\ DecLN \in POP(Nat \cup {qm}) /\ (DecLN \in POP(Nat \cup {qm}))' 
      /\ Inv /\ Inv'
      /\ [Next]_vars 
   => [Dec!Next]_(Dec!vars)
  <2> SUFFICES ASSUME FullTypeOK, DecLN \in POP(Nat \cup {qm}), DecLN' \in POP(Nat \cup {qm}),
                      Inv, Inv',
                      [Next]_vars
               PROVE  [Dec!Next]_(Dec!vars)
    \*OBVIOUS
  <2>. USE DEF FullTypeOK
  <2>1. ASSUME NEW self \in Procs,
               ncs(<<self>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. <<self>> \in ProcIds
      \*BY DEF ProcIds
    <3>1. DecPC[<<self>>] = "ncs"
      \*BY <2>1, DisjointIds DEF ncs, DecPC, DecProcSet
    <3>2. UNCHANGED << number, DecLN, localCh >>
      \*BY <2>1 DEF ncs, DecLN
    <3>3. DecPC' = [DecPC EXCEPT ![<<self>>] = "M"]
      BY <2>1, <3>2, DisjointIds DEF ncs, ProcSet, ProcIds, SubProcs, DecPC, DecProcSet
(*      <4>. DEFINE exc == [DecPC EXCEPT ![<<self>>] = "M"]
      <4>1. ASSUME NEW p \in DecProcSet
            PROVE  DecPC'[p] = exc[p]
        BY <2>1, <3>2, DisjointIds DEF ncs, DecPC, DecProcSet, ProcSet, ProcIds, SubProcs
      <4>. QED  BY <4>1(*, Zenon*) DEF DecPC
*)
    <3>4. Dec!ncs(<<self>>)
      \*BY <3>1, <3>2, <3>3 DEF Dec!ncs
    <3>. QED  BY <3>4, DecEqualities DEF Dec!Next, Dec!main, ProcIds
  <2>2. ASSUME NEW self \in Procs,
               M(<<self>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ <<self>> \in ProcIds
      \*BY DEF ProcIds
    <3>. PICK v \in Nat \ {0} :
           /\ pc[<<self>>] = "M"
           /\ \A j \in OtherProcs(self) : pc[<<self,j>>] = "L0"
           /\ \A j \in OtherProcs(self) : v > localNum[self][j]
           /\ number' = [number EXCEPT ![self] = v]
           /\ q' = [q EXCEPT ![self] = [j \in OtherProcs(self) |-> Append(q[self][j], v)]]
           /\ pc' = [pc EXCEPT ![<<self>>] = "L"]
           /\ UNCHANGED <<localNum, localCh, ackRcvd>>
      \*BY <2>2, SubProcsOfEquality(*, Isa*) DEF M, OtherProcs
    <3>1. DecPC[<<self>>] = "M"
      \*BY DisjointIds DEF DecPC, DecProcSet
    <3>2. \A p \in Dec!SubProcsOf(self) : DecPC[p] = "test"
      \*BY DecEqualities, DisjointIds DEF SubProcsOf, SubProcs, OtherProcs, DecPC, DecProcSet
    <3>3. \A j \in OtherProcs(self) : DecLN[self][j] # qm => v > DecLN[self][j]
      \*BY DEF DecLN, OtherProcs
    <3>4. DecLN' = [j \in Procs |-> [i \in OtherProcs(j) |->
                      IF i = self THEN qm ELSE DecLN[j][i]]]
      BY POP_access DEF POP, PFunc, Range, OtherProcs, DecLN
(*      <4>. SUFFICES ASSUME NEW j \in Procs, NEW i \in OtherProcs(j)
                    PROVE  DecLN'[j][i] = IF i = self THEN qm ELSE DecLN[j][i]
        BY (*Zenon*) DEF DecLN, OtherProcs
      <4>1. CASE i = self
        <5>. DEFINE g(x,y) == Append(q[x][y], v)
        <5>1. j \in OtherProcs(self)
          BY <4>1 DEF OtherProcs
        <5>2. q[self][j] \in Seq(Nat \cup {ack})
          BY <4>1, POP_access DEF OtherProcs
        <5>3. \A oth \in OtherProcs(self) :
                 /\ q[self][oth] \in Seq(Nat \cup {ack})
                 /\ g(self,oth) \in Seq(Nat \cup {ack})
          BY <4>1, POP_access
        <5>4. q'[self][j] = g(self,j)
          <6>1. q' = [q EXCEPT ![self] = [oth \in OtherProcs(self) |-> g(self,oth)]]
            OBVIOUS
          <6>. HIDE DEF g
          <6>. QED
            BY ONLY <5>1, <5>3, <6>1, POP_except_fun_value, FullTypeOK, IsaM("blast")
        <5>5. number'[self] \in Range(q'[self][j])
          BY <5>2, <5>4(*, Isa*) DEF Range
        <5>. QED  BY <4>1, <5>2, <5>5 DEF DecLN, OtherProcs
      <4>2. CASE i # self
        BY <4>2 DEF DecLN, OtherProcs, POP
      <4>. QED  BY <4>1, <4>2
*)
    <3>5. DecPC' = [DecPC EXCEPT ![<<self>>] = "L"]
      BY <3>4, DisjointIds, qmNotNat
      DEF ProcSet, ProcIds, SubProcs, OtherProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self>> THEN "L" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>2. CASE p \in ProcIds
        BY <4>2 DEF DecPC, ProcSet
      <4>3. CASE p \in SubProcs
        <5>. p \notin ProcIds
          BY <4>3, DisjointIds
        <5>. UNCHANGED pc[p]
          BY <4>3 DEF ProcSet
        <5>1. CASE p[1] = self
          <6>1. PICK oth \in OtherProcs(self) : p = <<self,oth>>
            BY <4>3, <5>1 DEF SubProcs, OtherProcs
          <6>2. DecPC[p] = "test"
            BY <4>3, <6>1 DEF DecPC
          <6>3. DecLN'[oth][self] = qm
            BY <3>4 DEF OtherProcs
          <6>4. DecPC'[p] = "test"
            BY <4>3, <6>1, <6>3, qmNotNat(*, Zenon*) DEF DecPC
          <6>. QED  BY <6>2, <6>4
        <5>2. CASE p[1] # self
          <6>1. UNCHANGED << DecLN[p[2]][p[1]], number[p[1]] >>
            BY <3>4, <4>3, <5>2 DEF SubProcs, OtherProcs
          <6>2. UNCHANGED pc[<<p[1]>>]
            BY <4>3, <5>2 DEF ProcIds, SubProcs, ProcSet
          <6>. QED  BY <4>3, <6>1, <6>2, DisjointIds DEF DecPC
        <5>. QED  BY <5>1, <5>2
      <4>4. CASE p \in WrProcs
        BY <4>4, DisjointIds DEF DecPC
      <4>. QED  BY <4>2, <4>3, <4>4 DEF DecProcSet
*)
    <3>6. Dec!M(<<self>>)
      \*BY <3>1, <3>2, <3>3, <3>4, <3>5, DecEqualities(*, Zenon*) DEF Dec!M
    <3>. QED  \*BY <3>6, DecEqualities DEF Dec!Next, Dec!main
  <2>3. ASSUME NEW self \in Procs,
               L(<<self>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self>>] = "L"
         /\ \A oth \in OtherProcs(self) : pc[<<self,oth>>] = "ch"
         /\ pc' = [pc EXCEPT ![<<self>>] = "cs"]
         /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>
      \*BY <2>3 DEF L, SubProcsOf, SubProcs, OtherProcs
    <3>. <<self>> \in ProcIds
      \*BY DEF ProcIds
    <3>1. DecPC[<<self>>] = "L"
      \*BY DEF DecPC, DecProcSet
    <3>2. \A p \in SubProcsOf(self) : DecPC[p] = "ch"
      \*BY DEF SubProcsOf, SubProcs, OtherProcs, DecPC, DecProcSet
    <3>3. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>4. DecPC' = [DecPC EXCEPT ![<<self>>] = "cs"]
      BY <3>3, DisjointIds
      DEF ProcSet, ProcIds, SubProcs, OtherProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self>> THEN "cs" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>1. CASE p \in ProcIds
        BY <4>1 DEF DecPC, ProcSet
      <4>2. CASE p \in SubProcs
        <5>. p \notin ProcIds
          BY <4>2, DisjointIds
        <5>. UNCHANGED pc[p]
          BY <4>2 DEF ProcSet
        <5>1. CASE p[1] = self
          BY <4>2, <5>1 DEF SubProcs, OtherProcs, DecPC
        <5>2. CASE p[1] # self
          BY <4>2, <5>2, <3>3 DEF DecPC, ProcIds, SubProcs, ProcSet
        <5>. QED  BY <5>1, <5>2
      <4>3. CASE p \in WrProcs
        BY <4>3, DisjointIds DEF DecPC
      <4>. QED  BY <4>1, <4>2, <4>3 DEF DecProcSet
*)
    <3>5. Dec!L(<<self>>)
      \*BY <3>1, <3>2, <3>3, <3>4, DecEqualities DEF Dec!L
    <3>. QED   \*BY <3>5, DecEqualities DEF Dec!Next, Dec!main
  <2>4. ASSUME NEW self \in Procs,
               cs(<<self>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self>>] = "cs"
         /\ pc' = [pc EXCEPT ![<<self>>] = "P"]
         /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>
      \*BY <2>4 DEF cs
    <3>. <<self>> \in ProcIds
      \*BY DEF ProcIds
    <3>1. DecPC[<<self>>] = "cs"
      \*BY DEF DecPC, DecProcSet
    <3>2. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>3. DecPC' = [DecPC EXCEPT ![<<self>>] = "P"]
      BY <3>2, DisjointIds DEF ProcSet, ProcIds, SubProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self>> THEN "P" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>1. CASE p \in ProcIds
        BY <4>1 DEF DecPC, ProcSet
      <4>2. CASE p \in SubProcs
        <5>. p \notin ProcIds
          BY <4>2, DisjointIds
        <5>. UNCHANGED pc[p]
          BY <4>2 DEF ProcSet
        <5>1. CASE p[1] = self
          BY <4>2, <5>1 DEF SubProcs, DecPC
        <5>2. CASE p[1] # self
          BY <4>2, <5>2, <3>2 DEF DecPC, ProcIds, SubProcs, ProcSet
        <5>. QED  BY <5>1, <5>2
      <4>3. CASE p \in WrProcs
        BY <4>3, DisjointIds DEF DecPC
      <4>. QED  BY <4>1, <4>2, <4>3 DEF DecProcSet
*)
    <3>4. Dec!cs(<<self>>)
      \*BY <3>1, <3>2, <3>3, DecEqualities DEF Dec!cs
    <3>. QED  \*BY <3>4, DecEqualities DEF Dec!Next, Dec!main
  <2>5. ASSUME NEW self \in Procs,
               P(<<self>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self>>] = "P"
         /\ number' = [number EXCEPT ![self] = 0]
         /\ q' = [q EXCEPT ![self] = [j \in OtherProcs(self) |-> Append(q[self][j], 0)]]
         /\ pc' = [pc EXCEPT ![<<self>>] = "ncs"]
         /\ UNCHANGED << localNum, localCh >>
      \*BY <2>5 DEF P
    <3>. <<self>> \in ProcIds
      \*BY DEF ProcIds
    <3>1. DecPC[<<self>>] = "P"
      \*BY DEF DecPC, DecProcSet
    <3>2. DecLN' = [j \in Procs |-> [i \in OtherProcs(j) |->
                      IF i = self THEN qm ELSE DecLN[j][i]]]
      BY POP_access DEF POP, PFunc, Range, OtherProcs, DecLN
(*      <4>. SUFFICES ASSUME NEW j \in Procs, NEW i \in OtherProcs(j)
                    PROVE  DecLN'[j][i] = IF i = self THEN qm ELSE DecLN[j][i]
        BY (*Zenon*) DEF DecLN
      <4>1. CASE i = self
        <5>. DEFINE g(x,y) == Append(q[x][y], 0)
        <5>1. j \in OtherProcs(self)
          BY <4>1 DEF OtherProcs
        <5>2. q[self][j] \in Seq(Nat \cup {ack})
          BY <4>1, POP_access DEF OtherProcs
        <5>3. \A oth \in OtherProcs(self) :
                 /\ q[self][oth] \in Seq(Nat \cup {ack})
                 /\ g(self,oth) \in Seq(Nat \cup {ack})
          BY <4>1, POP_access
        <5>4. q'[self][j] = g(self,j)
          <6>1. q' = [q EXCEPT ![self] = [oth \in OtherProcs(self) |-> g(self,oth)]]
            OBVIOUS
          <6>. HIDE DEF g
          <6>. QED
            BY ONLY <5>1, <5>3, <6>1, POP_except_fun_value, FullTypeOK, IsaM("blast")
        <5>5. number'[self] \in Range(q'[self][j])
          BY <5>2, <5>4(*, Isa*) DEF Range
        <5>. QED  BY <4>1, <5>2, <5>5 DEF DecLN, OtherProcs
      <4>2. CASE i # self
        BY <4>2 DEF DecLN, OtherProcs, POP
      <4>. QED  BY <4>1, <4>2
*)
    <3>3. DecPC' = [DecPC EXCEPT ![<<self>>] = "ncs"]
      BY <3>2, DisjointIds DEF ProcSet, ProcIds, SubProcs, OtherProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self>> THEN "ncs" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>1. CASE p \in ProcIds
        BY <4>1 DEF DecPC, ProcSet
      <4>2. CASE p \in SubProcs
        <5>. p \notin ProcIds
          BY <4>2, DisjointIds
        <5>. UNCHANGED pc[p]
          BY <4>2 DEF ProcSet
        <5>1. CASE p[1] = self
          BY <4>2, <5>1(*, Zenon*) DEF SubProcs, OtherProcs, DecPC
        <5>2. CASE p[1] # self
          <6>. UNCHANGED pc[<<p[1]>>]
            BY <4>2, <5>2 DEF ProcIds, SubProcs, ProcSet
          <6>. UNCHANGED DecLN[p[2]][p[1]]
            BY <5>2, <4>2, <3>2 DEF SubProcs, OtherProcs
          <6>. QED  BY DEF DecPC, DecProcSet, ProcIds, SubProcs
        <5>. QED  BY <5>1, <5>2
      <4>3. CASE p \in WrProcs
        BY <4>3, DisjointIds DEF DecPC
      <4>. QED  BY <4>1, <4>2, <4>3 DEF DecProcSet
*)
    <3>4. Dec!P(<<self>>)
      \*BY <3>1, <3>2, <3>3, DecEqualities DEF Dec!P
    <3>. QED  \*BY <3>4, DecEqualities DEF Dec!Next, Dec!main
  <2>6. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               ch(<<self,oth>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self,oth>>] = "ch"
         /\ pc[<<self>>] = "M"
         /\ localCh' = [localCh EXCEPT ![oth][self] = 1]
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L0"]
         /\ UNCHANGED << number, localNum, ackRcvd, q >>
      \*BY <2>6 DEF ch
    <3>. <<self,oth>> \in SubProcs \ ProcIds
      \*BY DEF SubProcs, ProcIds, OtherProcs
    <3>1. DecPC[<<self,oth>>] = "ch"
      \*BY DEF DecPC, DecProcSet
    <3>2. DecPC[<<self>>] = "M"
      \*BY DEF DecPC, DecProcSet, ProcIds
    <3>3. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>4. DecPC' = [DecPC EXCEPT ![<<self,oth>>] = "test"]
      BY <3>3, DisjointIds DEF ProcSet, ProcIds, SubProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self,oth>> THEN "test" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>. QED  BY <3>3, DisjointIds DEF DecPC, DecProcSet, ProcIds, SubProcs, ProcSet
*)
    <3>5. Dec!ch(<<self,oth>>)
      \*BY <3>1, <3>2, <3>3, <3>4, DecEqualities DEF Dec!ch
    <3>. QED  \*BY <3>5, DecEqualities DEF Dec!Next, Dec!sub
  <2>7. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L0(<<self,oth>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self,oth>>] = "L0"
         /\ pc[<<self>>] = "L"
         /\ ackRcvd[self][oth] = 1
         /\ localCh' = [localCh EXCEPT ![oth][self] = 0]
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L2"]
         /\ UNCHANGED << number, localNum, ackRcvd, q >>
      \*BY <2>7 DEF L0
    <3>. <<self,oth>> \in SubProcs \ ProcIds
      \*BY DEF SubProcs, ProcIds, OtherProcs
    <3>1. DecPC[<<self,oth>>] = "Lb"
      \*BY DEF Inv, DecPC, DecProcSet, DecLN, ProcSet, OtherProcs
    <3>2. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>3. DecPC' = [DecPC EXCEPT ![<<self,oth>>] = "L2"]
      BY <3>2, DisjointIds DEF ProcSet, ProcIds, SubProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self,oth>> THEN "L2" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>. QED  BY <3>2, DisjointIds DEF DecPC, DecProcSet, ProcIds, SubProcs, ProcSet
*)
    <3>4. Dec!Lb(<<self,oth>>)
      \*BY <3>1, <3>2, <3>3, DecEqualities DEF Dec!Lb
    <3>. QED  \*BY <3>4, DecEqualities DEF Dec!Next, Dec!sub
  <2>8. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L2(<<self,oth>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self,oth>>] = "L2"
         /\ localCh[self][oth] = 0
         /\ pc' = [pc EXCEPT ![<<self,oth>>] = "L3"]
         /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>
      \*BY <2>8 DEF L2
    <3>. <<self,oth>> \in SubProcs \ ProcIds
      \*BY DEF SubProcs, ProcIds, OtherProcs
    <3>1. DecPC[<<self,oth>>] = "L2"
      \*BY DEF DecPC, DecProcSet
    <3>2. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>3. DecPC' = [DecPC EXCEPT ![<<self,oth>>] = "L3"]
      BY <3>2, DisjointIds DEF ProcSet, ProcIds, SubProcs, DecProcSet, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self,oth>> THEN "L3" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>. QED  BY <3>2, DisjointIds DEF DecPC, DecProcSet, ProcIds, SubProcs, ProcSet
*)
    <3>4. Dec!L2(<<self,oth>>)
      \*BY <3>1, <3>2, <3>3, DecEqualities DEF Dec!L2
    <3>. QED  \*BY <3>4, DecEqualities DEF Dec!Next, Dec!sub
  <2>9. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
               L3(<<self,oth>>)
        PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self,oth>>] = "L3"
            /\ \/ localNum[self][oth] = 0
               \/ <<number[self], self>> \ll <<localNum[self][oth], oth>>
            /\ pc' = [pc EXCEPT ![<<self,oth>>] = "ch"]
            /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>
      \*BY <2>9 DEF L3
    <3>. <<self,oth>> \in SubProcs \ ProcIds
      \*BY DEF SubProcs, ProcIds, OtherProcs
    <3>1. DecPC[<<self,oth>>] = "L3"
      \*BY DEF DecPC, DecProcSet
    <3>a. ASSUME DecLN[self][oth] \notin {0,qm}
          PROVE  <<number[self], self>> \ll <<DecLN[self][oth], oth>>
      \*BY <3>a DEF DecLN
    <3>2. UNCHANGED DecLN
      \*BY DEF DecLN
    <3>3. DecPC' = [DecPC EXCEPT ![<<self,oth>>] = "ch"]
      BY <3>2, DisjointIds DEF ProcSet, ProcIds, SubProcs, DecPC
(*      <4>. SUFFICES ASSUME NEW p \in DecProcSet
                    PROVE  DecPC'[p] = IF p = <<self,oth>> THEN "ch" ELSE DecPC[p]
        BY (*Zenon*) DEF DecPC
      <4>. QED  BY <3>2, DisjointIds DEF DecPC, DecProcSet, ProcIds, SubProcs, ProcSet
*)
    <3>4. Dec!L3(<<self,oth>>)
      \*BY <3>1, <3>a, <3>2, <3>3, DecEqualities DEF Dec!L3
    <3>. QED  \*BY <3>4, DecEqualities DEF Dec!Next, Dec!sub
  <2>10. ASSUME NEW self \in Procs, NEW oth \in OtherProcs(self),
                msg(<<self,oth,"msg">>)
         PROVE  [Dec!Next]_(Dec!vars)
    <3>. /\ pc[<<self,oth,"msg">>] = "wr"
         /\ q[oth][self] # << >>
         /\ LET v == Head(q[oth][self]) IN
                /\ IF v = ack
                   THEN /\ ackRcvd' = [ackRcvd EXCEPT ![self][oth] = 1]
                        /\ UNCHANGED localNum
                   ELSE /\ localNum' = [localNum EXCEPT ![self][oth] = v]
                        /\ UNCHANGED ackRcvd
                /\ IF v \in {0, ack}
                   THEN q' = [q EXCEPT ![oth][self] = Tail(q[oth][self])]
                   ELSE q' = [q EXCEPT ![oth][self] = Tail(q[oth][self]),
                                       ![self][oth] = Append(q[self][oth], ack)]
         /\ UNCHANGED << pc, number, localCh >>
      \*BY <2>10 DEF msg, wr
    <3>. DEFINE v == Head(q[oth][self])
    <3>1. CASE v = ack
      BY <3>1, POP_access, ackNotNat, RangeHeadTail
      DEF POP, PFunc, OtherProcs, DecPC, DecLN, Dec!vars
(*      <4>1. ASSUME NEW i \in Procs, NEW j \in OtherProcs(i) 
            PROVE  number'[j] \in Range(q'[j][i]) <=> number[j] \in Range(q[j][i])
        <5>1. CASE i = self /\ j = oth
          <6>. q[j][i] \in Seq(Nat \cup {ack})
            BY POP_access DEF OtherProcs
          <6>1. q'[j][i] = Tail(q[j][i])
            BY <3>1, <5>1(*, Isa*) DEF POP, PFunc, OtherProcs
          <6>4. Range(q'[j][i]) \cup {ack} = Range(q[j][i])
            BY <3>1, <5>1, <6>1, RangeHeadTail
          <6>5. number[j] # ack
            BY ackNotNat DEF OtherProcs
          <6>. QED  BY <6>4, <6>5
        <5>2. CASE ~(i = self /\ j = oth)
          BY <3>1, <5>2 DEF POP, PFunc, OtherProcs
        <5>. QED  BY <5>1, <5>2
      <4>2. UNCHANGED DecLN
        BY <3>1, <4>1 DEF DecLN
      <4>3. UNCHANGED DecPC
        BY <4>2 DEF DecPC
      <4>4. UNCHANGED Dec!vars
        BY <4>2, <4>3 DEF Dec!vars
      <4>. QED  BY <4>4
*)
    <3>2. CASE v = 0 /\ number[oth] = 0
      \* FIXME not simplifying further
      <4>. <<oth,self,"wr">> \in WrProcs \ (ProcIds \cup SubProcs)
        \*BY DisjointIds DEF WrProcs, OtherProcs
      <4>1. DecPC[<<oth,self,"wr">>] = "wr"
        \*BY DEF DecPC, DecProcSet
      <4>2. DecLN[self][oth] = qm
        \*BY <3>2, POP_access, RangeHeadTail DEF DecLN, OtherProcs
      <4>3. /\ pc[<<oth>>] \in {"ncs", "M"}
            /\ DecPC[<<oth>>] = pc[<<oth>>]
        \*BY <3>2 DEF DecPC, DecProcSet, Inv, OtherProcs, ProcIds
      <4>4. DecLN' = [DecLN EXCEPT ![self][oth] = 0]
        \* Can the proof of this step be simplified?
        BY <3>2, POP_access, ackNotNat
        DEF Inv, POP, PFunc, Range, OtherProcs, DecLN
(*        <5>1. SUFFICES ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
                       PROVE  DecLN'[i][j] = IF i = self /\ j = oth THEN 0 ELSE DecLN[i][j]
          BY POP_except_equal(*, Isa*)
        <5>2. q' = [q EXCEPT ![oth][self] = Tail(q[oth][self])]
          BY <3>2
        <5>3. localNum' = [localNum EXCEPT ![self][oth] = 0]
          BY <3>2, ackNotNat
        <5>4. CASE i = self /\ j = oth
          <6>1. q'[oth][self] = Tail(q[oth][self])
            BY <5>2 DEF POP, PFunc, OtherProcs
          <6>2. /\ 1 \in 1 .. Len(q[oth][self])
                /\ number[oth] = q[oth][self][1]
            BY <3>2, POP_access DEF OtherProcs
          <6>. q[oth][self] \in Seq(Nat \cup {ack})
            BY POP_access DEF OtherProcs
          <6>3. ASSUME number[oth] \in Range(Tail(q[oth][self]))
                PROVE  FALSE
            <7>. DEFINE tl == Tail(q[oth][self])
            <7>1. PICK k \in 1 .. Len(tl) : tl[k] = number[oth]
              BY <6>3 DEF Range
            <7>2. /\ k+1 \in 1 .. Len(q[oth][self])
                  /\ q[oth][self][k+1] = number[oth]
              BY <7>1
            <7>3. Inv!4!(oth)!(self)
              BY DEF Inv, OtherProcs
            <7>. QED  BY <6>2, <7>2, <7>3
          <6>. QED  BY <5>3, <5>4, <6>1, <6>3 DEF DecLN, POP, PFunc
        <5>5. CASE ~(i = self /\ j = oth)
          BY <5>2, <5>3, <5>5 DEF DecLN, OtherProcs, POP
        <5>. QED  BY <5>4, <5>5
*)
      <4>5. DecPC' = [DecPC EXCEPT ![<<oth,self,"wr">>] = "wr"]
        BY <4>3, <4>4, DisjointIds DEF POP, SubProcs, OtherProcs, DecProcSet, DecPC
(*        <5>. SUFFICES ASSUME NEW p \in DecProcSet
                      PROVE  DecPC'[p] = IF p = <<oth,self,"wr">> THEN "wr" ELSE DecPC[p]
          BY (*Zenon*) DEF DecPC
        <5>1. CASE p \in ProcIds
          BY <5>1 DEF DecPC
        <5>2. CASE p \in SubProcs
          <6>. PICK i,j \in Procs : i # j /\ p = <<i,j>>
            BY <5>2 DEF SubProcs
          <6>1. DecPC[p] = IF pc[p] = "L0"
                           THEN IF pc[<<i>>] = "L" /\ DecLN[j][i] = number[i]
                                THEN "Lb" ELSE "test"
                           ELSE pc[p]
            BY <5>2, DisjointIds DEF DecPC, DecProcSet
          <6>2. DecPC'[p] = IF pc[p] = "L0"
                            THEN IF pc[<<i>>] = "L" /\ DecLN'[j][i] = number[i]
                                 THEN "Lb" ELSE "test"
                            ELSE pc[p]
            BY <5>2, DisjointIds DEF DecPC, DecProcSet
          <6>3. pc[<<i>>] = "L" => DecLN'[j][i] = DecLN[j][i]
            BY <4>3, <4>4 DEF OtherProcs, POP
          <6>. QED  BY <6>1, <6>2, <6>3
        <5>3. CASE p \in WrProcs
          BY <5>3, DisjointIds DEF DecPC
        <5>. QED  BY <5>1, <5>2, <5>3 DEF DecProcSet
*)
      <4>6. Dec!wr(<<oth,self,"wr">>)
        \*BY <4>1, <4>2, <4>3, <4>4, <4>5, DecEqualities DEF Dec!wr
      <4>. QED  \*BY <4>6, DecEqualities DEF Dec!Next, Dec!wrp
    <3>3. CASE v = 0 /\ number[oth] # 0
      <4>1. /\ localNum' = [localNum EXCEPT ![self][oth] = 0]
            /\ q' = [q EXCEPT ![oth][self] = Tail(q[oth][self])]
        \*BY <3>3, ackNotNat
      <4>2. UNCHANGED DecLN
        BY <3>3, <4>1, POP_except, POP_access, RangeHeadTail
        DEF Inv, POP, OtherProcs, DecLN
(*        <5>. SUFFICES ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
                      PROVE  DecLN'[i][j] = DecLN[i][j]
          BY DEF DecLN
        <5>1. CASE i = self /\ j = oth
          <6>1. localNum'[self][oth] # number'[oth]
            BY <3>3, <4>1, POP_except(*, Isa*)
          <6>2. Inv!3!(oth)!(self)'
            BY DEF OtherProcs, Inv
          <6>3. number'[oth] \in Range(q'[oth][self])
            BY <3>3, <6>1, <6>2
          <6>4. /\ q[oth][self] \in Seq(Nat \cup {ack})
                /\ Tail(q[oth][self]) \in Seq(Nat \cup {ack})
            BY POP_access DEF OtherProcs
          <6>5. q'[oth][self] = Tail(q[oth][self])
            BY <4>1, <6>4, FullTypeOK, POP_except(*, Isa*) DEF OtherProcs
          <6>6. number[oth] \in Range(q[oth][self])
            BY <3>3, <4>1, <6>3, <6>4, <6>5, RangeHeadTail
          <6>. QED  BY <5>1, <6>3, <6>6 DEF DecLN
        <5>2. CASE ~(i = self /\ j = oth)
          BY <4>1, <5>2 DEF DecLN, OtherProcs, POP
        <5>. QED  BY <5>1, <5>2
*)
      <4>3. UNCHANGED DecPC
        \*BY <4>2 DEF DecPC
      <4>. QED  \*BY <4>2, <4>3 DEF Dec!vars
    <3>4. CASE v \in Nat \ {0}
      <4>. <<oth,self>> \in SubProcs \ (ProcIds \cup WrProcs)
        \*BY DisjointIds DEF SubProcs, OtherProcs
      <4>1. q[oth][self] \in Seq(Nat \cup {ack})
        \*BY POP_access DEF OtherProcs
      <4>2. /\ 1 \in 1 .. Len(q[oth][self])
            /\ v = q[oth][self][1]
        \*BY <4>1
      <4>3. /\ Inv!3!(oth)!(self)
            /\ Inv!4!(oth)!(self)
        \*BY DEF OtherProcs, Inv
      <4>4. v = number[oth]
        \*BY <3>4, <4>2, <4>3(*, Zenon*)
      <4>5. number[oth] \in Nat
        \*BY DEF OtherProcs
      <4>6. number[oth] \in Range(q[oth][self])
        \*BY <4>1, <4>2, <4>4, RangeEquality
      <4>7. /\ pc[<<oth>>] = "L"
            /\ pc[<<oth,self>>] = "L0"
        \*BY <3>4, <4>1, <4>3, <4>6
      <4>8. DecLN[self][oth] = qm
        \*BY <4>6 DEF DecLN
      <4>9. /\ DecPC[<<oth,self>>] = "test"
            /\ DecPC[<<oth>>] = "L"
        \*BY <4>7, <4>8, qmNotNat(*, Zenon*) DEF DecPC, DecProcSet, OtherProcs, ProcIds
      <4>10. DecLN' = [DecLN EXCEPT ![self][oth] = number[oth]]
        BY <3>4, <4>1, <4>2, <4>3, <4>4, <4>5,
           POP_except, POP_access, POP_except_equal,
           AppendProperties, ackNotNat
        DEF POP, PFunc, OtherProcs, Range, DecLN
(*        <5>1. localNum' = [localNum EXCEPT ![self][oth] = number[oth]]
          BY <3>4, <4>4, ackNotNat
        <5>2. /\ q' \in POP(Seq(Nat \cup {ack}))
              /\ \A k \in Procs : \A l \in OtherProcs(k) :
                    q'[k][l] = IF k = self /\ l = oth THEN Append(q[self][oth], ack)
                               ELSE IF k = oth /\ l = self THEN Tail(q[oth][self])
                               ELSE q[k][l]
          <6>. DEFINE tl == Tail(q[oth][self])
                      qq == [q EXCEPT ![oth][self] = tl]
          <6>1. tl \in Seq(Nat \cup {ack})
            BY <4>1
          <6>2. q' = [qq EXCEPT ![self][oth] = Append(q[self][oth], ack)]
            BY <3>4, ackNotNat
          <6>. HIDE DEF tl
          <6>3. qq \in POP(Seq(Nat \cup {ack}))
            BY ONLY FullTypeOK, <6>1, POP_except(*, Zenon*) DEF OtherProcs
          <6>4. qq[oth][self] = tl
            BY ONLY FullTypeOK, <6>1, POP_except(*, Isa*) DEF OtherProcs
          <6>5. \A k \in Procs : \A l \in OtherProcs(k) :
                   k # oth \/ l # self => qq[k][l] = q[k][l]
            BY ONLY FullTypeOK, <6>1, POP_except DEF OtherProcs
          <6>. HIDE DEF qq
          <6>6. Append(q[self][oth], ack) \in Seq(Nat \cup {ack})
            BY POP_access
          <6>7. /\ q' \in POP(Seq(Nat \cup {ack}))
                /\ q'[self][oth] = Append(q[self][oth], ack)
                /\ \A k \in Procs : \A l \in OtherProcs(k) :
                      k # self \/ l # oth => q'[k][l] = qq[k][l]
            BY ONLY <6>2, <6>3, <6>6, POP_except(*, Isa*)
          <6>8. ASSUME NEW k \in Procs, NEW l \in OtherProcs(k)
                PROVE  q'[k][l] = IF k = self /\ l = oth THEN Append(q[self][oth], ack)
                                  ELSE IF k = oth /\ l = self THEN Tail(q[oth][self])
                                  ELSE q[k][l]
            <7>1. CASE k = self /\ l = oth
              BY <7>1, <6>7
            <7>2. CASE k = oth /\ l = self
              BY <7>2, <6>7, <6>4 DEF OtherProcs, tl
            <7>3. CASE ~(k = self /\ l = oth) /\ ~(k = oth /\ l = self)
              BY <7>3, <6>7, <6>5 DEF OtherProcs
            <7>. QED  BY <7>1, <7>2, <7>3
          <6>. QED  BY <6>7, <6>8
        <5>3. SUFFICES ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
                       PROVE  DecLN'[i][j] = IF i = self /\ j = oth THEN number[oth] ELSE DecLN[i][j]
          BY <4>5, POP_except_equal(*, Isa*)
        <5>4. CASE i = self /\ j = oth
          <6>3. ASSUME number[oth] \in Range(Tail(q[oth][self]))
                PROVE  FALSE
            <7>. DEFINE tl == Tail(q[oth][self])
            <7>1. PICK k \in 1 .. Len(tl) : tl[k] = number[oth]
              BY <4>1, <6>3 DEF Range
            <7>2. /\ k+1 \in 1 .. Len(q[oth][self])
                  /\ q[oth][self][k+1] = number[oth]
              BY <4>1, <7>1
            <7>. QED  BY ONLY <4>2, <4>3, <4>4, <7>2
          <6>. QED  BY <5>1, <5>4, <5>2, <6>3 DEF DecLN, POP, PFunc, OtherProcs
        <5>5. CASE i = oth /\ j = self
          <6>1. /\ q[self][oth] \in Seq(Nat \cup {ack})
                /\ q'[self][oth] = Append(q[self][oth], ack)
             BY <5>2, POP_access(*, Zenon*) DEF OtherProcs
          <6>2. number'[self] \in Range(q'[self][oth]) <=> number[self] \in Range(q[self][oth])
            BY <6>1, AppendProperties, ackNotNat DEF OtherProcs, Range
          <6>3. localNum'[oth][self] = localNum[oth][self]
            BY <4>5, <5>1, POP_except DEF OtherProcs
          <6>. QED  BY <5>5, <6>2, <6>3 DEF DecLN, OtherProcs
        <5>6. CASE ~(i = self /\ j = oth) /\ ~(i = oth /\ j = self)
          <6>1. q'[j][i] = q[j][i]
            BY <5>6, <5>2 DEF OtherProcs
          <6>2. localNum'[i][j] = localNum[i][j]
            BY <5>6, <4>5, <5>1, POP_except DEF OtherProcs
          <6>. QED  BY <5>6, <6>1, <6>2 DEF DecLN
        <5>. QED  BY <5>4, <5>5, <5>6
*)
      <4>11. DecPC' = [DecPC EXCEPT ![<<oth,self>>] = "Lb"]
        BY <4>5, <4>7, <4>10, POP_except, DisjointIds
        DEF SubProcs, OtherProcs, DecProcSet, DecPC
(*        <5>. SUFFICES ASSUME NEW p \in DecProcSet
                      PROVE  DecPC'[p] = IF p = <<oth,self>> THEN "Lb" ELSE DecPC[p]
          BY (*Zenon*) DEF DecPC
        <5>1. CASE p \in ProcIds
          BY <5>1 DEF DecPC
        <5>2. CASE p \in SubProcs
          <6>. PICK i,j \in Procs : i # j /\ p = <<i,j>>
            BY <5>2 DEF SubProcs
          <6>1. CASE i = oth /\ j = self
            <7>. DecLN'[self][oth] = number'[oth]
              BY <4>10, <4>5, POP_except(*, Isa*)
            <7>. QED  BY <5>2, <6>1, <4>7, DisjointIds DEF DecPC
          <6>2. CASE ~(i = oth /\ j = self)
            <7>. DecLN'[j][i] = DecLN[j][i]
              BY <4>10, <4>5, <6>2, POP_except DEF OtherProcs
            <7>. QED  BY <5>2, <6>2, DisjointIds DEF DecPC
          <6>. QED  BY <6>1, <6>2
        <5>3. CASE p \in WrProcs
          BY <5>3, DisjointIds DEF DecPC
        <5>. QED  BY <5>1, <5>2, <5>3 DEF DecProcSet
*)
      <4>12. Dec!test(<<oth,self>>)
        \*BY <4>9, <4>10, <4>11, DecEqualities DEF Dec!test
      <4>. QED  \*BY <4>12, DecEqualities DEF Dec!Next, Dec!sub
    <3>. QED  \*BY <3>1, <3>2, <3>3, <3>4, POP_access DEF OtherProcs
  <2>11. CASE UNCHANGED vars
    \*BY <2>11 DEF vars, Dec!vars, DecLN, DecPC
  <2>12. QED
    \*BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
    \*   DEF Next, main, sub, ProcIds, SubProcs, MsgProcs, OtherProcs
<1>. QED
  \*BY <1>1, <1>2, Typing, DecLN_type, Invariance, PTL DEF Spec, DecSafety


=============================================================================
\* Modification History
\* Last modified Fri Jan 28 17:26:40 CET 2022 by adefourn
\* Last modified Tue Nov 16 18:51:45 CET 2021 by merz
\* Created Thu Sep 02 11:41:20 CEST 2021 by merz
