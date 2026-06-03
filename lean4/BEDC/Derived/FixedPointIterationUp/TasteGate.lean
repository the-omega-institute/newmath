import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FixedPointIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FixedPointIterationUp : Type where
  | mk (X d T x0 I R H C P N : BHist) : FixedPointIterationUp
  deriving DecidableEq

def fixedPointIterationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fixedPointIterationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fixedPointIterationEncodeBHist h

def fixedPointIterationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fixedPointIterationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fixedPointIterationDecodeBHist tail)

private theorem fixedPointIteration_decode_encode_bhist :
    ∀ h : BHist,
      fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fixedPointIterationFields : FixedPointIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FixedPointIterationUp.mk X d T x0 I R H C P N => [X, d, T, x0, I, R, H, C, P, N]

def fixedPointIterationToEventFlow : FixedPointIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fixedPointIterationFields x).map fixedPointIterationEncodeBHist

private def fixedPointIterationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fixedPointIterationEventAtDefault index rest

def fixedPointIterationFromEventFlow
    (ef : EventFlow) : Option FixedPointIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FixedPointIterationUp.mk
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 0 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 1 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 2 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 3 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 4 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 5 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 6 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 7 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 8 ef))
      (fixedPointIterationDecodeBHist (fixedPointIterationEventAtDefault 9 ef)))

private theorem fixedPointIteration_round_trip :
    ∀ x : FixedPointIterationUp,
      fixedPointIterationFromEventFlow (fixedPointIterationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d T x0 I R H C P N =>
      change
        some
          (FixedPointIterationUp.mk
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist X))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist d))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist T))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist x0))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist I))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist R))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist H))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist C))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist P))
            (fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist N))) =
          some (FixedPointIterationUp.mk X d T x0 I R H C P N)
      rw [fixedPointIteration_decode_encode_bhist X,
        fixedPointIteration_decode_encode_bhist d,
        fixedPointIteration_decode_encode_bhist T,
        fixedPointIteration_decode_encode_bhist x0,
        fixedPointIteration_decode_encode_bhist I,
        fixedPointIteration_decode_encode_bhist R,
        fixedPointIteration_decode_encode_bhist H,
        fixedPointIteration_decode_encode_bhist C,
        fixedPointIteration_decode_encode_bhist P,
        fixedPointIteration_decode_encode_bhist N]

private theorem fixedPointIterationToEventFlow_injective
    {x y : FixedPointIterationUp} :
    fixedPointIterationToEventFlow x = fixedPointIterationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fixedPointIterationFromEventFlow (fixedPointIterationToEventFlow x) =
        fixedPointIterationFromEventFlow (fixedPointIterationToEventFlow y) :=
    congrArg fixedPointIterationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fixedPointIteration_round_trip x).symm
      (Eq.trans hread (fixedPointIteration_round_trip y)))

private theorem fixedPointIteration_field_faithful :
    ∀ x y : FixedPointIterationUp,
      fixedPointIterationFields x = fixedPointIterationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X d T x0 I R H C P N =>
      cases y with
      | mk X' d' T' x0' I' R' H' C' P' N' =>
          cases hfields
          rfl

instance fixedPointIterationBHistCarrier : BHistCarrier FixedPointIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fixedPointIterationToEventFlow
  fromEventFlow := fixedPointIterationFromEventFlow

instance fixedPointIterationChapterTasteGate : ChapterTasteGate FixedPointIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fixedPointIterationFromEventFlow (fixedPointIterationToEventFlow x) = some x
    exact fixedPointIteration_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fixedPointIterationToEventFlow_injective heq)

instance fixedPointIterationFieldFaithful : FieldFaithful FixedPointIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fixedPointIterationFields
  field_faithful := fixedPointIteration_field_faithful

instance fixedPointIterationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FixedPointIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FixedPointIterationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FixedPointIterationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FixedPointIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fixedPointIterationChapterTasteGate

theorem FixedPointIterationTasteGate_single_carrier_alignment :
    (∀ h : BHist, fixedPointIterationDecodeBHist (fixedPointIterationEncodeBHist h) = h) ∧
      (∀ x : FixedPointIterationUp,
        fixedPointIterationFromEventFlow (fixedPointIterationToEventFlow x) = some x) ∧
      (∀ x y : FixedPointIterationUp,
        fixedPointIterationToEventFlow x = fixedPointIterationToEventFlow y → x = y) ∧
      fixedPointIterationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fixedPointIteration_decode_encode_bhist
  constructor
  · exact fixedPointIteration_round_trip
  constructor
  · intro x y heq
    exact fixedPointIterationToEventFlow_injective heq
  · rfl

end BEDC.Derived.FixedPointIterationUp
