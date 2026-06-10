import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedObservationTotalHostUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedObservationTotalHostUp : Type where
  | mk (A T S F R H C P N : BHist) : ClosedObservationTotalHostUp
  deriving DecidableEq

def closedObservationTotalHostEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedObservationTotalHostEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedObservationTotalHostEncodeBHist h

def closedObservationTotalHostDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedObservationTotalHostDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedObservationTotalHostDecodeBHist tail)

private theorem closedObservationTotalHost_decode_encode_bhist :
    ∀ h : BHist,
      closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedObservationTotalHostFields : ClosedObservationTotalHostUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedObservationTotalHostUp.mk A T S F R H C P N => [A, T, S, F, R, H, C, P, N]

def closedObservationTotalHostToEventFlow : ClosedObservationTotalHostUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedObservationTotalHostFields x).map closedObservationTotalHostEncodeBHist

private def closedObservationTotalHostEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedObservationTotalHostEventAtDefault index rest

def closedObservationTotalHostFromEventFlow
    (ef : EventFlow) : Option ClosedObservationTotalHostUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedObservationTotalHostUp.mk
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 0 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 1 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 2 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 3 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 4 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 5 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 6 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 7 ef))
      (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEventAtDefault 8 ef)))

private theorem closedObservationTotalHost_round_trip (x : ClosedObservationTotalHostUp) :
    closedObservationTotalHostFromEventFlow (closedObservationTotalHostToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A T S F R H C P N =>
      change
        some
          (ClosedObservationTotalHostUp.mk
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist A))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist T))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist S))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist F))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist R))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist H))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist C))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist P))
            (closedObservationTotalHostDecodeBHist (closedObservationTotalHostEncodeBHist N))) =
          some (ClosedObservationTotalHostUp.mk A T S F R H C P N)
      rw [closedObservationTotalHost_decode_encode_bhist A,
        closedObservationTotalHost_decode_encode_bhist T,
        closedObservationTotalHost_decode_encode_bhist S,
        closedObservationTotalHost_decode_encode_bhist F,
        closedObservationTotalHost_decode_encode_bhist R,
        closedObservationTotalHost_decode_encode_bhist H,
        closedObservationTotalHost_decode_encode_bhist C,
        closedObservationTotalHost_decode_encode_bhist P,
        closedObservationTotalHost_decode_encode_bhist N]

private theorem closedObservationTotalHostToEventFlow_injective
    {x y : ClosedObservationTotalHostUp} :
    closedObservationTotalHostToEventFlow x = closedObservationTotalHostToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedObservationTotalHostFromEventFlow (closedObservationTotalHostToEventFlow x) =
        closedObservationTotalHostFromEventFlow (closedObservationTotalHostToEventFlow y) :=
    congrArg closedObservationTotalHostFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedObservationTotalHost_round_trip x).symm
      (Eq.trans hread (closedObservationTotalHost_round_trip y)))

private theorem closedObservationTotalHost_fields_faithful :
    ∀ x y : ClosedObservationTotalHostUp,
      closedObservationTotalHostFields x = closedObservationTotalHostFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk A₁ T₁ S₁ F₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ T₂ S₂ F₂ R₂ H₂ C₂ P₂ N₂ =>
          injection h with hA t1
          injection t1 with hT t2
          injection t2 with hS t3
          injection t3 with hF t4
          injection t4 with hR t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hA
          cases hT
          cases hS
          cases hF
          cases hR
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance closedObservationTotalHostBHistCarrier : BHistCarrier ClosedObservationTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedObservationTotalHostToEventFlow
  fromEventFlow := closedObservationTotalHostFromEventFlow

instance closedObservationTotalHostChapterTasteGate :
    ChapterTasteGate ClosedObservationTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedObservationTotalHostFromEventFlow (closedObservationTotalHostToEventFlow x) =
      some x
    exact closedObservationTotalHost_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedObservationTotalHostToEventFlow_injective heq)

instance closedObservationTotalHostFieldFaithful : FieldFaithful ClosedObservationTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedObservationTotalHostFields
  field_faithful := closedObservationTotalHost_fields_faithful

instance closedObservationTotalHostNontrivial : Nontrivial ClosedObservationTotalHostUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedObservationTotalHostUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedObservationTotalHostUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ClosedObservationTotalHost_taste_gate : ChapterTasteGate ClosedObservationTotalHostUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedObservationTotalHostChapterTasteGate

end BEDC.Derived.ClosedObservationTotalHostUp
