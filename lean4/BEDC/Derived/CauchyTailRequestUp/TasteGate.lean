import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailRequestUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailRequestUp : Type where
  | mk (W Q D R E H C P N : BHist) : CauchyTailRequestUp
  deriving DecidableEq

def cauchyTailRequestEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailRequestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailRequestEncodeBHist h

def cauchyTailRequestDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailRequestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailRequestDecodeBHist tail)

private theorem CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailRequestFields : CauchyTailRequestUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailRequestUp.mk W Q D R E H C P N => [W, Q, D, R, E, H, C, P, N]

def cauchyTailRequestToEventFlow : CauchyTailRequestUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailRequestFields x).map cauchyTailRequestEncodeBHist

def cauchyTailRequestFromEventFlow : EventFlow -> Option CauchyTailRequestUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: Q :: D :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyTailRequestUp.mk
          (cauchyTailRequestDecodeBHist W)
          (cauchyTailRequestDecodeBHist Q)
          (cauchyTailRequestDecodeBHist D)
          (cauchyTailRequestDecodeBHist R)
          (cauchyTailRequestDecodeBHist E)
          (cauchyTailRequestDecodeBHist H)
          (cauchyTailRequestDecodeBHist C)
          (cauchyTailRequestDecodeBHist P)
          (cauchyTailRequestDecodeBHist N))
  | _ => none

private theorem CauchyTailRequestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyTailRequestUp,
      cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W Q D R E H C P N =>
      change
        some
          (CauchyTailRequestUp.mk
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist W))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist Q))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist D))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist R))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist E))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist H))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist C))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist P))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist N))) =
          some (CauchyTailRequestUp.mk W Q D R E H C P N)
      rw [CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode W,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode R,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode E,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTailRequestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailRequestUp} :
    cauchyTailRequestToEventFlow x = cauchyTailRequestToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) =
        cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow y) :=
    congrArg cauchyTailRequestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailRequestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailRequestTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTailRequestTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyTailRequestUp, cauchyTailRequestFields x = cauchyTailRequestFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance cauchyTailRequestBHistCarrier : BHistCarrier CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailRequestToEventFlow
  fromEventFlow := cauchyTailRequestFromEventFlow

instance cauchyTailRequestChapterTasteGate : ChapterTasteGate CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) = some x
    exact CauchyTailRequestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailRequestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTailRequestFieldFaithful : FieldFaithful CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailRequestFields
  field_faithful := CauchyTailRequestTasteGate_single_carrier_alignment_fields

instance cauchyTailRequestNontrivial : Nontrivial CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailRequestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailRequestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyTailRequestTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist h) = h) ∧
      cauchyTailRequestEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      cauchyTailRequestEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyTailRequestTasteGate_single_carrier_alignment_decode_encode,
      rfl,
      rfl⟩

end BEDC.Derived.CauchyTailRequestUp.TasteGate
