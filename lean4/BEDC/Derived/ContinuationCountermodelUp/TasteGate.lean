import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationCountermodelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationCountermodelUp : Type where
  | mk
      (finiteFit admissible modelPrediction observedContinuation mismatch stability failure
        transport replay provenance name : BHist) :
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
  | ContinuationCountermodelUp.mk finiteFit admissible modelPrediction observedContinuation
      mismatch stability failure transport replay provenance name =>
      [[BMark.b0],
        continuationCountermodelEncodeBHist finiteFit,
        [BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist admissible,
        [BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist modelPrediction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist observedContinuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist mismatch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist failure,
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
        continuationCountermodelEncodeBHist name]

def continuationCountermodelFromEventFlow : EventFlow → Option ContinuationCountermodelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | finiteFit :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | admissible :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | modelPrediction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | observedContinuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | mismatch :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | stability :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | failure :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | replay :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ContinuationCountermodelUp.mk
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    finiteFit)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    admissible)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    modelPrediction)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    observedContinuation)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    mismatch)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    stability)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    failure)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    transport)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    replay)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    provenance)
                                                                                                  (continuationCountermodelDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem continuationCountermodel_round_trip :
    ∀ x : ContinuationCountermodelUp,
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk finiteFit admissible modelPrediction observedContinuation mismatch stability failure
      transport replay provenance name =>
      change
        some
          (ContinuationCountermodelUp.mk
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist finiteFit))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist admissible))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist modelPrediction))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist observedContinuation))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist mismatch))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist stability))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist failure))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist transport))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist replay))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist provenance))
            (continuationCountermodelDecodeBHist
              (continuationCountermodelEncodeBHist name))) =
          some
            (ContinuationCountermodelUp.mk finiteFit admissible modelPrediction
              observedContinuation mismatch stability failure transport replay provenance name)
      rw [continuationCountermodelDecode_encode_bhist finiteFit,
        continuationCountermodelDecode_encode_bhist admissible,
        continuationCountermodelDecode_encode_bhist modelPrediction,
        continuationCountermodelDecode_encode_bhist observedContinuation,
        continuationCountermodelDecode_encode_bhist mismatch,
        continuationCountermodelDecode_encode_bhist stability,
        continuationCountermodelDecode_encode_bhist failure,
        continuationCountermodelDecode_encode_bhist transport,
        continuationCountermodelDecode_encode_bhist replay,
        continuationCountermodelDecode_encode_bhist provenance,
        continuationCountermodelDecode_encode_bhist name]

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

instance continuationCountermodelBHistCarrier : BHistCarrier ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationCountermodelToEventFlow
  fromEventFlow := continuationCountermodelFromEventFlow

instance continuationCountermodelChapterTasteGate :
    ChapterTasteGate ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
      some x
    exact continuationCountermodel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationCountermodelToEventFlow_injective heq)

instance continuationCountermodelFieldFaithful : FieldFaithful ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ContinuationCountermodelUp.mk finiteFit admissible modelPrediction observedContinuation
        mismatch stability failure transport replay provenance name =>
        [finiteFit, admissible, modelPrediction, observedContinuation, mismatch, stability,
          failure, transport, replay, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk finiteFit₁ admissible₁ modelPrediction₁ observedContinuation₁ mismatch₁ stability₁
        failure₁ transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk finiteFit₂ admissible₂ modelPrediction₂ observedContinuation₂ mismatch₂ stability₂
            failure₂ transport₂ replay₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance continuationCountermodelNontrivial : Nontrivial ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationCountermodelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuationCountermodelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContinuationCountermodelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationCountermodelChapterTasteGate

theorem ContinuationCountermodelTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist h) = h) ∧
      (∀ x : ContinuationCountermodelUp,
        continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
          some x) ∧
        (∀ x y : ContinuationCountermodelUp,
          continuationCountermodelToEventFlow x = continuationCountermodelToEventFlow y →
            x = y) ∧
          continuationCountermodelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨continuationCountermodelDecode_encode_bhist, continuationCountermodel_round_trip,
      fun _x _y heq => continuationCountermodelToEventFlow_injective heq, rfl⟩

end BEDC.Derived.ContinuationCountermodelUp
