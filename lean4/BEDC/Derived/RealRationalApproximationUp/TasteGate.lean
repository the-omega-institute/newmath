import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealRationalApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealRationalApproximationUp : Type where
  | mk (R Q D S G A H C P N : BHist) : RealRationalApproximationUp
  deriving DecidableEq

def realRationalApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realRationalApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realRationalApproximationEncodeBHist h

def realRationalApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realRationalApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realRationalApproximationDecodeBHist tail)

private theorem realRationalApproximationDecode_encode_bhist :
    ∀ h : BHist, realRationalApproximationDecodeBHist
      (realRationalApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realRationalApproximationFields :
    RealRationalApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealRationalApproximationUp.mk R Q D S G A H C P N =>
      [R, Q, D, S, G, A, H, C, P, N]

def realRationalApproximationToEventFlow :
    RealRationalApproximationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realRationalApproximationFields x).map realRationalApproximationEncodeBHist

private def realRationalApproximationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realRationalApproximationEventAtDefault index rest

def realRationalApproximationFromEventFlow
    (ef : EventFlow) : Option RealRationalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealRationalApproximationUp.mk
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 0 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 1 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 2 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 3 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 4 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 5 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 6 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 7 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 8 ef))
      (realRationalApproximationDecodeBHist
        (realRationalApproximationEventAtDefault 9 ef)))

private theorem realRationalApproximation_round_trip :
    ∀ x : RealRationalApproximationUp,
      realRationalApproximationFromEventFlow
        (realRationalApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q D S G A H C P N =>
      change
        some
          (RealRationalApproximationUp.mk
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist R))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist Q))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist D))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist S))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist G))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist A))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist H))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist C))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist P))
            (realRationalApproximationDecodeBHist
              (realRationalApproximationEncodeBHist N))) =
          some (RealRationalApproximationUp.mk R Q D S G A H C P N)
      rw [realRationalApproximationDecode_encode_bhist R,
        realRationalApproximationDecode_encode_bhist Q,
        realRationalApproximationDecode_encode_bhist D,
        realRationalApproximationDecode_encode_bhist S,
        realRationalApproximationDecode_encode_bhist G,
        realRationalApproximationDecode_encode_bhist A,
        realRationalApproximationDecode_encode_bhist H,
        realRationalApproximationDecode_encode_bhist C,
        realRationalApproximationDecode_encode_bhist P,
        realRationalApproximationDecode_encode_bhist N]

private theorem realRationalApproximationToEventFlow_injective
    {x y : RealRationalApproximationUp} :
    realRationalApproximationToEventFlow x =
      realRationalApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) =
        realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow y) :=
    congrArg realRationalApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realRationalApproximation_round_trip x).symm
      (Eq.trans hread (realRationalApproximation_round_trip y)))

private theorem realRationalApproximation_fields_faithful :
    ∀ x y : RealRationalApproximationUp,
      realRationalApproximationFields x =
        realRationalApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 Q1 D1 S1 G1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 Q2 D2 S2 G2 A2 H2 C2 P2 N2 =>
          injection hfields with hR t1
          injection t1 with hQ t2
          injection t2 with hD t3
          injection t3 with hS t4
          injection t4 with hG t5
          injection t5 with hA t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hR
          cases hQ
          cases hD
          cases hS
          cases hG
          cases hA
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance realRationalApproximationBHistCarrier :
    BHistCarrier RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realRationalApproximationToEventFlow
  fromEventFlow := realRationalApproximationFromEventFlow

instance realRationalApproximationChapterTasteGate :
    ChapterTasteGate RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) =
        some x
    exact realRationalApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realRationalApproximationToEventFlow_injective heq)

instance realRationalApproximationFieldFaithful :
    FieldFaithful RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realRationalApproximationFields
  field_faithful := realRationalApproximation_fields_faithful

instance realRationalApproximationNontrivial :
    Nontrivial RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealRationalApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealRationalApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealRationalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realRationalApproximationChapterTasteGate

theorem RealRationalApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist, realRationalApproximationDecodeBHist
      (realRationalApproximationEncodeBHist h) = h) ∧
      (∀ x : RealRationalApproximationUp,
        realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) = some x) ∧
        (∀ x y : RealRationalApproximationUp,
          realRationalApproximationToEventFlow x =
            realRationalApproximationToEventFlow y → x = y) ∧
          realRationalApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨realRationalApproximationDecode_encode_bhist,
      realRationalApproximation_round_trip,
      (fun _ _ heq => realRationalApproximationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealRationalApproximationUp
