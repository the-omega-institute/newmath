import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakLawLargeNumbersUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakLawLargeNumbersUp : Type where
  | mk (P R A V T E H C Q N : BHist) : WeakLawLargeNumbersUp
  deriving DecidableEq

def WeakLawLargeNumbersTasteGate_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: WeakLawLargeNumbersTasteGate_encodeBHist h
  | BHist.e1 h => BMark.b1 :: WeakLawLargeNumbersTasteGate_encodeBHist h

def WeakLawLargeNumbersTasteGate_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (WeakLawLargeNumbersTasteGate_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (WeakLawLargeNumbersTasteGate_decodeBHist tail)

private theorem WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      WeakLawLargeNumbersTasteGate_decodeBHist
        (WeakLawLargeNumbersTasteGate_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def WeakLawLargeNumbersTasteGate_fields : WeakLawLargeNumbersUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakLawLargeNumbersUp.mk P R A V T E H C Q N => [P, R, A, V, T, E, H, C, Q, N]

def WeakLawLargeNumbersTasteGate_toEventFlow : WeakLawLargeNumbersUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (WeakLawLargeNumbersTasteGate_fields x).map WeakLawLargeNumbersTasteGate_encodeBHist

private def WeakLawLargeNumbersTasteGate_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => WeakLawLargeNumbersTasteGate_eventAt index rest

def WeakLawLargeNumbersTasteGate_fromEventFlow
    (flow : EventFlow) : Option WeakLawLargeNumbersUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeakLawLargeNumbersUp.mk
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 0 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 1 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 2 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 3 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 4 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 5 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 6 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 7 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 8 flow))
      (WeakLawLargeNumbersTasteGate_decodeBHist (WeakLawLargeNumbersTasteGate_eventAt 9 flow)))

private theorem WeakLawLargeNumbersTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeakLawLargeNumbersUp,
      WeakLawLargeNumbersTasteGate_fromEventFlow
        (WeakLawLargeNumbersTasteGate_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P R A V T E H C Q N =>
      change
        some
          (WeakLawLargeNumbersUp.mk
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist P))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist R))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist A))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist V))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist T))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist E))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist H))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist C))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist Q))
            (WeakLawLargeNumbersTasteGate_decodeBHist
              (WeakLawLargeNumbersTasteGate_encodeBHist N))) =
          some (WeakLawLargeNumbersUp.mk P R A V T E H C Q N)
      rw [WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode P,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode R,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode A,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode V,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode T,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode E,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode H,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode C,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode Q,
        WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode N]

private theorem WeakLawLargeNumbersTasteGate_toEventFlow_injective
    {x y : WeakLawLargeNumbersUp} :
    WeakLawLargeNumbersTasteGate_toEventFlow x =
      WeakLawLargeNumbersTasteGate_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      WeakLawLargeNumbersTasteGate_fromEventFlow
          (WeakLawLargeNumbersTasteGate_toEventFlow x) =
        WeakLawLargeNumbersTasteGate_fromEventFlow
          (WeakLawLargeNumbersTasteGate_toEventFlow y) :=
    congrArg WeakLawLargeNumbersTasteGate_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WeakLawLargeNumbersTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeakLawLargeNumbersTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeakLawLargeNumbersTasteGate_field_faithful :
    ∀ x y : WeakLawLargeNumbersUp,
      WeakLawLargeNumbersTasteGate_fields x = WeakLawLargeNumbersTasteGate_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 R1 A1 V1 T1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 R2 A2 V2 T2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance weakLawLargeNumbersBHistCarrier : BHistCarrier WeakLawLargeNumbersUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := WeakLawLargeNumbersTasteGate_toEventFlow
  fromEventFlow := WeakLawLargeNumbersTasteGate_fromEventFlow

instance weakLawLargeNumbersChapterTasteGate :
    ChapterTasteGate WeakLawLargeNumbersUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      WeakLawLargeNumbersTasteGate_fromEventFlow
        (WeakLawLargeNumbersTasteGate_toEventFlow x) = some x
    exact WeakLawLargeNumbersTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeakLawLargeNumbersTasteGate_toEventFlow_injective heq)

instance weakLawLargeNumbersFieldFaithful : FieldFaithful WeakLawLargeNumbersUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := WeakLawLargeNumbersTasteGate_fields
  field_faithful := WeakLawLargeNumbersTasteGate_field_faithful

instance weakLawLargeNumbersNontrivial : Nontrivial WeakLawLargeNumbersUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WeakLawLargeNumbersUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WeakLawLargeNumbersUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WeakLawLargeNumbersUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakLawLargeNumbersChapterTasteGate

def taste_gate_witness : FieldFaithful WeakLawLargeNumbersUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakLawLargeNumbersFieldFaithful

theorem WeakLawLargeNumbersTasteGate_single_carrier_alignment :
    (forall h : BHist,
      WeakLawLargeNumbersTasteGate_decodeBHist
        (WeakLawLargeNumbersTasteGate_encodeBHist h) = h) ∧
      WeakLawLargeNumbersTasteGate_fields
        (WeakLawLargeNumbersUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨WeakLawLargeNumbersTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.WeakLawLargeNumbersUp
