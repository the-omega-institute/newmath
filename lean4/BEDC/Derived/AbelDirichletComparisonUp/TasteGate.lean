import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelDirichletComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelDirichletComparisonUp : Type where
  | mk
      (seriesSource abelFace dirichletFace sharedTail readback endpoint transport replay
        provenance localName : BHist) :
      AbelDirichletComparisonUp

def abelDirichletComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelDirichletComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelDirichletComparisonEncodeBHist h

def abelDirichletComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelDirichletComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelDirichletComparisonDecodeBHist tail)

private theorem abelDirichletComparison_decode_encode_bhist :
    ∀ h : BHist,
      abelDirichletComparisonDecodeBHist (abelDirichletComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abelDirichletComparisonFields : AbelDirichletComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelDirichletComparisonUp.mk seriesSource abelFace dirichletFace sharedTail readback
      endpoint transport replay provenance localName =>
      [seriesSource, abelFace, dirichletFace, sharedTail, readback, endpoint, transport, replay,
        provenance, localName]

def abelDirichletComparisonToEventFlow : AbelDirichletComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (abelDirichletComparisonFields x).map abelDirichletComparisonEncodeBHist

private def abelDirichletComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelDirichletComparisonEventAtDefault index rest

def abelDirichletComparisonFromEventFlow
    (flow : EventFlow) : Option AbelDirichletComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelDirichletComparisonUp.mk
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 0 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 1 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 2 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 3 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 4 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 5 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 6 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 7 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 8 flow))
      (abelDirichletComparisonDecodeBHist (abelDirichletComparisonEventAtDefault 9 flow)))

private theorem abelDirichletComparison_round_trip :
    ∀ x : AbelDirichletComparisonUp,
      abelDirichletComparisonFromEventFlow
        (abelDirichletComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk seriesSource abelFace dirichletFace sharedTail readback endpoint transport replay
      provenance localName =>
      change
        some
          (AbelDirichletComparisonUp.mk
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist seriesSource))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist abelFace))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist dirichletFace))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist sharedTail))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist readback))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist endpoint))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist transport))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist replay))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist provenance))
            (abelDirichletComparisonDecodeBHist
              (abelDirichletComparisonEncodeBHist localName))) =
          some
            (AbelDirichletComparisonUp.mk seriesSource abelFace dirichletFace sharedTail
              readback endpoint transport replay provenance localName)
      rw [abelDirichletComparison_decode_encode_bhist seriesSource,
        abelDirichletComparison_decode_encode_bhist abelFace,
        abelDirichletComparison_decode_encode_bhist dirichletFace,
        abelDirichletComparison_decode_encode_bhist sharedTail,
        abelDirichletComparison_decode_encode_bhist readback,
        abelDirichletComparison_decode_encode_bhist endpoint,
        abelDirichletComparison_decode_encode_bhist transport,
        abelDirichletComparison_decode_encode_bhist replay,
        abelDirichletComparison_decode_encode_bhist provenance,
        abelDirichletComparison_decode_encode_bhist localName]

private theorem abelDirichletComparisonToEventFlow_injective
    {x y : AbelDirichletComparisonUp} :
    abelDirichletComparisonToEventFlow x = abelDirichletComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelDirichletComparisonFromEventFlow (abelDirichletComparisonToEventFlow x) =
        abelDirichletComparisonFromEventFlow (abelDirichletComparisonToEventFlow y) :=
    congrArg abelDirichletComparisonFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (abelDirichletComparison_round_trip x).symm
        (Eq.trans hread (abelDirichletComparison_round_trip y)))

instance abelDirichletComparisonBHistCarrier :
    BHistCarrier AbelDirichletComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelDirichletComparisonToEventFlow
  fromEventFlow := abelDirichletComparisonFromEventFlow

instance abelDirichletComparisonChapterTasteGate :
    ChapterTasteGate AbelDirichletComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      abelDirichletComparisonFromEventFlow
        (abelDirichletComparisonToEventFlow x) = some x
    exact abelDirichletComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (abelDirichletComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AbelDirichletComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelDirichletComparisonChapterTasteGate

theorem AbelDirichletComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      abelDirichletComparisonDecodeBHist (abelDirichletComparisonEncodeBHist h) = h) ∧
      (∀ x : AbelDirichletComparisonUp,
        abelDirichletComparisonFromEventFlow
          (abelDirichletComparisonToEventFlow x) = some x) ∧
        (∀ x y : AbelDirichletComparisonUp,
          abelDirichletComparisonToEventFlow x = abelDirichletComparisonToEventFlow y →
            x = y) ∧
          abelDirichletComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨abelDirichletComparison_decode_encode_bhist,
      abelDirichletComparison_round_trip,
      (fun _ _ heq => abelDirichletComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AbelDirichletComparisonUp
