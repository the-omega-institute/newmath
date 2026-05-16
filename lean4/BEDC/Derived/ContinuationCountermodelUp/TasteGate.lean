import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationCountermodelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationCountermodelUp : Type where
  | mk (finiteFit admissibleContinuation modelPrediction observedContinuation mismatch
      stability failureSurface transport replay provenance localName : BHist) :
      ContinuationCountermodelUp
  deriving DecidableEq

def continuationCountermodelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationCountermodelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationCountermodelEncodeBHist h

def continuationCountermodelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationCountermodelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationCountermodelDecodeBHist tail)

private theorem continuationCountermodelDecode_encode_bhist :
    ∀ h : BHist,
      continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def continuationCountermodelToEventFlow : ContinuationCountermodelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationCountermodelUp.mk finiteFit admissibleContinuation modelPrediction
      observedContinuation mismatch stability failureSurface transport replay provenance
      localName =>
      [[BMark.b0],
        continuationCountermodelEncodeBHist finiteFit,
        [BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist admissibleContinuation,
        [BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist modelPrediction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist observedContinuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist mismatch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist failureSurface,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        continuationCountermodelEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist localName]

def continuationCountermodelFromEventFlow : EventFlow → Option ContinuationCountermodelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, finiteFit, _tag1, admissibleContinuation, _tag2, modelPrediction,
      _tag3, observedContinuation, _tag4, mismatch, _tag5, stability, _tag6,
      failureSurface, _tag7, transport, _tag8, replay, _tag9, provenance, _tag10,
      localName] =>
      some
        (ContinuationCountermodelUp.mk
          (continuationCountermodelDecodeBHist finiteFit)
          (continuationCountermodelDecodeBHist admissibleContinuation)
          (continuationCountermodelDecodeBHist modelPrediction)
          (continuationCountermodelDecodeBHist observedContinuation)
          (continuationCountermodelDecodeBHist mismatch)
          (continuationCountermodelDecodeBHist stability)
          (continuationCountermodelDecodeBHist failureSurface)
          (continuationCountermodelDecodeBHist transport)
          (continuationCountermodelDecodeBHist replay)
          (continuationCountermodelDecodeBHist provenance)
          (continuationCountermodelDecodeBHist localName))
  | _ => none

private theorem continuationCountermodel_round_trip :
    ∀ x : ContinuationCountermodelUp,
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk finiteFit admissibleContinuation modelPrediction observedContinuation mismatch
      stability failureSurface transport replay provenance localName =>
      change
        some
          (ContinuationCountermodelUp.mk
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist finiteFit))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist admissibleContinuation))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist modelPrediction))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist observedContinuation))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist mismatch))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist stability))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist failureSurface))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist transport))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist replay))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist provenance))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist localName))) =
          some
            (ContinuationCountermodelUp.mk finiteFit admissibleContinuation modelPrediction
              observedContinuation mismatch stability failureSurface transport replay
              provenance localName)
      rw [continuationCountermodelDecode_encode_bhist finiteFit,
        continuationCountermodelDecode_encode_bhist admissibleContinuation,
        continuationCountermodelDecode_encode_bhist modelPrediction,
        continuationCountermodelDecode_encode_bhist observedContinuation,
        continuationCountermodelDecode_encode_bhist mismatch,
        continuationCountermodelDecode_encode_bhist stability,
        continuationCountermodelDecode_encode_bhist failureSurface,
        continuationCountermodelDecode_encode_bhist transport,
        continuationCountermodelDecode_encode_bhist replay,
        continuationCountermodelDecode_encode_bhist provenance,
        continuationCountermodelDecode_encode_bhist localName]

private theorem continuationCountermodelToEventFlow_injective
    {x y : ContinuationCountermodelUp} :
    continuationCountermodelToEventFlow x = continuationCountermodelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
        continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow y) :=
    congrArg continuationCountermodelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationCountermodel_round_trip x).symm
      (Eq.trans hread (continuationCountermodel_round_trip y)))

instance continuationCountermodel_bhist_carrier :
    BHistCarrier ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationCountermodelToEventFlow
  fromEventFlow := continuationCountermodelFromEventFlow

instance continuationCountermodelChapterTasteGate :
    ChapterTasteGate ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
        some x
    exact continuationCountermodel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationCountermodelToEventFlow_injective heq)

instance continuationCountermodelFieldFaithful :
    FieldFaithful ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ContinuationCountermodelUp.mk finiteFit admissibleContinuation modelPrediction
        observedContinuation mismatch stability failureSurface transport replay provenance
        localName =>
        [finiteFit, admissibleContinuation, modelPrediction, observedContinuation, mismatch,
          stability, failureSurface, transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk finiteFit₁ admissibleContinuation₁ modelPrediction₁ observedContinuation₁ mismatch₁
        stability₁ failureSurface₁ transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | mk finiteFit₂ admissibleContinuation₂ modelPrediction₂ observedContinuation₂ mismatch₂
            stability₂ failureSurface₂ transport₂ replay₂ provenance₂ localName₂ =>
            simp only [] at h
            cases h
            rfl

instance continuationCountermodelNontrivial : Nontrivial ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationCountermodelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuationCountermodelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.ContinuationCountermodelUp
