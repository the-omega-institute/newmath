import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterCriterionUp : Type where
  | mk
      (base cauchy metric uniform window rat dyadic real transport replay provenance name :
        BHist) :
      CauchyFilterCriterionUp
  deriving DecidableEq

def cauchyFilterCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterCriterionEncodeBHist h

def cauchyFilterCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterCriterionDecodeBHist tail)

private theorem cauchyFilterCriterion_decode_encode_bhist :
    ∀ h : BHist,
      cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterCriterionFields : CauchyFilterCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterCriterionUp.mk base cauchy metric uniform window rat dyadic real transport
      replay provenance name =>
      [base, cauchy, metric, uniform, window, rat, dyadic, real, transport, replay,
        provenance, name]

def cauchyFilterCriterionToEventFlow : CauchyFilterCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterCriterionFields x).map cauchyFilterCriterionEncodeBHist

private def cauchyFilterCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterCriterionEventAt index rest

def cauchyFilterCriterionFromEventFlow
    (flow : EventFlow) : Option CauchyFilterCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterCriterionUp.mk
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 0 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 1 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 2 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 3 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 4 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 5 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 6 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 7 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 8 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 9 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 10 flow))
      (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEventAt 11 flow)))

private theorem cauchyFilterCriterion_round_trip :
    ∀ x : CauchyFilterCriterionUp,
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk base cauchy metric uniform window rat dyadic real transport replay provenance name =>
      change
        some
          (CauchyFilterCriterionUp.mk
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist base))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist cauchy))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist metric))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist uniform))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist window))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist rat))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist dyadic))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist real))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist transport))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist replay))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist provenance))
            (cauchyFilterCriterionDecodeBHist (cauchyFilterCriterionEncodeBHist name))) =
          some
            (CauchyFilterCriterionUp.mk base cauchy metric uniform window rat dyadic real
              transport replay provenance name)
      rw [cauchyFilterCriterion_decode_encode_bhist base,
        cauchyFilterCriterion_decode_encode_bhist cauchy,
        cauchyFilterCriterion_decode_encode_bhist metric,
        cauchyFilterCriterion_decode_encode_bhist uniform,
        cauchyFilterCriterion_decode_encode_bhist window,
        cauchyFilterCriterion_decode_encode_bhist rat,
        cauchyFilterCriterion_decode_encode_bhist dyadic,
        cauchyFilterCriterion_decode_encode_bhist real,
        cauchyFilterCriterion_decode_encode_bhist transport,
        cauchyFilterCriterion_decode_encode_bhist replay,
        cauchyFilterCriterion_decode_encode_bhist provenance,
        cauchyFilterCriterion_decode_encode_bhist name]

private theorem cauchyFilterCriterionToEventFlow_injective
    {x y : CauchyFilterCriterionUp} :
    cauchyFilterCriterionToEventFlow x = cauchyFilterCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) =
        cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow y) :=
    congrArg cauchyFilterCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterCriterion_round_trip x).symm
      (Eq.trans hread (cauchyFilterCriterion_round_trip y)))

instance cauchyFilterCriterionBHistCarrier :
    BHistCarrier CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterCriterionToEventFlow
  fromEventFlow := cauchyFilterCriterionFromEventFlow

instance cauchyFilterCriterionChapterTasteGate :
    ChapterTasteGate CauchyFilterCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterCriterionFromEventFlow (cauchyFilterCriterionToEventFlow x) = some x
    exact cauchyFilterCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyFilterCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterCriterionChapterTasteGate

theorem CauchyFilterCriterionTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier CauchyFilterCriterionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate CauchyFilterCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyFilterCriterionBHistCarrier⟩
  · exact ⟨cauchyFilterCriterionChapterTasteGate⟩

end BEDC.Derived.CauchyFilterCriterionUp
