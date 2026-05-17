import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceSocketUp : Type where
  | mk :
      (T K U A S R H C P N : BHist) →
        MachineInterfaceSocketUp
  deriving DecidableEq

def machineInterfaceSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceSocketEncodeBHist h

def machineInterfaceSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceSocketDecodeBHist tail)

theorem machineInterfaceSocketDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def machineInterfaceSocketRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => machineInterfaceSocketRawAt n rest

private theorem machineInterfaceSocket_mk_congr
    {T T' K K' U U' A A' S S' R R' H H' C C' P P' N N' : BHist}
    (hT : T' = T)
    (hK : K' = K)
    (hU : U' = U)
    (hA : A' = A)
    (hS : S' = S)
    (hR : R' = R)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    MachineInterfaceSocketUp.mk T' K' U' A' S' R' H' C' P' N' =
      MachineInterfaceSocketUp.mk T K U A S R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hK
  cases hU
  cases hA
  cases hS
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def machineInterfaceSocketToEventFlow : MachineInterfaceSocketUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineInterfaceSocketUp.mk T K U A S R H C P N =>
      [machineInterfaceSocketEncodeBHist T,
        machineInterfaceSocketEncodeBHist K,
        machineInterfaceSocketEncodeBHist U,
        machineInterfaceSocketEncodeBHist A,
        machineInterfaceSocketEncodeBHist S,
        machineInterfaceSocketEncodeBHist R,
        machineInterfaceSocketEncodeBHist H,
        machineInterfaceSocketEncodeBHist C,
        machineInterfaceSocketEncodeBHist P,
        machineInterfaceSocketEncodeBHist N]

def machineInterfaceSocketFromEventFlow :
    EventFlow → Option MachineInterfaceSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MachineInterfaceSocketUp.mk
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 0 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 1 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 2 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 3 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 4 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 5 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 6 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 7 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 8 ef))
        (machineInterfaceSocketDecodeBHist (machineInterfaceSocketRawAt 9 ef)))

def machineInterfaceSocketFields : MachineInterfaceSocketUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineInterfaceSocketUp.mk T K U A S R H C P N =>
      [T, K, U, A, S, R, H, C, P, N]

theorem machineInterfaceSocket_round_trip :
    ∀ x : MachineInterfaceSocketUp,
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T K U A S R H C P N =>
      exact
        congrArg some
          (machineInterfaceSocket_mk_congr
            (machineInterfaceSocketDecode_encode_bhist T)
            (machineInterfaceSocketDecode_encode_bhist K)
            (machineInterfaceSocketDecode_encode_bhist U)
            (machineInterfaceSocketDecode_encode_bhist A)
            (machineInterfaceSocketDecode_encode_bhist S)
            (machineInterfaceSocketDecode_encode_bhist R)
            (machineInterfaceSocketDecode_encode_bhist H)
            (machineInterfaceSocketDecode_encode_bhist C)
            (machineInterfaceSocketDecode_encode_bhist P)
            (machineInterfaceSocketDecode_encode_bhist N))

theorem machineInterfaceSocketToEventFlow_injective :
    ∀ x y : MachineInterfaceSocketUp,
      machineInterfaceSocketToEventFlow x = machineInterfaceSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hxy
  have optionEq : some x = some y := by
    calc
      some x =
          machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) :=
        (machineInterfaceSocket_round_trip x).symm
      _ =
          machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow y) :=
        congrArg machineInterfaceSocketFromEventFlow hxy
      _ = some y := machineInterfaceSocket_round_trip y
  exact Option.some.inj optionEq

instance machineInterfaceSocketBHistCarrier : BHistCarrier MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceSocketToEventFlow
  fromEventFlow := machineInterfaceSocketFromEventFlow

instance machineInterfaceSocketChapterTasteGate :
    ChapterTasteGate MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x
    exact machineInterfaceSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceSocketToEventFlow_injective x y heq)

instance machineInterfaceSocketNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceSocketUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceSocketUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

instance machineInterfaceSocketFieldFaithful :
    FieldFaithful MachineInterfaceSocketUp where
  fields := machineInterfaceSocketFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk T1 K1 U1 A1 S1 R1 H1 C1 P1 N1 =>
        cases y with
        | mk T2 K2 U2 A2 S2 R2 H2 C2 P2 N2 =>
            injection h with hT t1
            injection t1 with hK t2
            injection t2 with hU t3
            injection t3 with hA t4
            injection t4 with hS t5
            injection t5 with hR t6
            injection t6 with hH t7
            injection t7 with hC t8
            injection t8 with hP t9
            injection t9 with hN _
            cases hT
            cases hK
            cases hU
            cases hA
            cases hS
            cases hR
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

def taste_gate : ChapterTasteGate MachineInterfaceSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceSocketChapterTasteGate

end BEDC.Derived.MachineInterfaceSocketUp
