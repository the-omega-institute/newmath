import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationCountermodelUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
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

theorem ContinuationCountermodelUp_root_replay_transport
    {root reuse replay defeat routed : BHist} :
    Cont root reuse replay ->
      Cont replay defeat routed ->
        UnaryHistory root ->
          UnaryHistory reuse ->
            UnaryHistory defeat ->
              UnaryHistory replay ∧ UnaryHistory routed ∧ Cont root reuse replay ∧
                Cont replay defeat routed := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro rootReuseReplay replayDefeatRouted rootUnary reuseUnary defeatUnary
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed rootUnary reuseUnary rootReuseReplay
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed replayUnary defeatUnary replayDefeatRouted
  exact ⟨replayUnary, routedUnary, rootReuseReplay, replayDefeatRouted⟩

theorem ContinuationCountermodelNameCertObligations
    {finiteFit admissible modelPrediction observedContinuation mismatch stability failure
      _transport replay provenance _name routed : BHist} :
    Cont finiteFit admissible replay ->
      Cont modelPrediction observedContinuation mismatch ->
        Cont replay mismatch routed ->
          UnaryHistory finiteFit ->
            UnaryHistory admissible ->
              UnaryHistory modelPrediction ->
                UnaryHistory observedContinuation ->
                  UnaryHistory stability ->
                    UnaryHistory failure ->
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row finiteFit ∨ hsame row admissible ∨
                            hsame row modelPrediction ∨ hsame row observedContinuation ∨
                              hsame row mismatch ∨ hsame row replay ∨ hsame row routed)
                        (fun row : BHist =>
                          hsame row finiteFit ∨ hsame row admissible ∨
                            hsame row modelPrediction ∨ hsame row observedContinuation ∨
                              hsame row mismatch ∨ hsame row replay ∨ hsame row routed)
                        (fun row : BHist => UnaryHistory row ∧ hsame provenance provenance)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro finiteAdmissibleReplay modelObservedMismatch replayMismatchRouted finiteUnary
    admissibleUnary modelUnary observedUnary _stabilityUnary _failureUnary
  have mismatchUnary : UnaryHistory mismatch :=
    unary_cont_closed modelUnary observedUnary modelObservedMismatch
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed finiteUnary admissibleUnary finiteAdmissibleReplay
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed replayUnary mismatchUnary replayMismatchRouted
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro finiteFit (Or.inl (hsame_refl finiteFit))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases source with
        | inl sameFinite =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameFinite)
        | inr rest =>
            cases rest with
            | inl sameAdmissible =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameAdmissible))
            | inr rest =>
                cases rest with
                | inl sameModel =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameModel)))
                | inr rest =>
                    cases rest with
                    | inl sameObserved =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameObserved))))
                    | inr rest =>
                        cases rest with
                        | inl sameMismatch =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows)
                                        sameMismatch)))))
                        | inr rest =>
                            cases rest with
                            | inl sameReplay =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm sameRows)
                                              sameReplay))))))
                            | inr sameRouted =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (hsame_trans (hsame_symm sameRows)
                                              sameRouted))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro row source
      cases source with
      | inl sameFinite =>
          exact
            And.intro (unary_transport finiteUnary (hsame_symm sameFinite))
              (hsame_refl provenance)
      | inr rest =>
          cases rest with
          | inl sameAdmissible =>
              exact
                And.intro (unary_transport admissibleUnary (hsame_symm sameAdmissible))
                  (hsame_refl provenance)
          | inr rest =>
              cases rest with
              | inl sameModel =>
                  exact
                    And.intro (unary_transport modelUnary (hsame_symm sameModel))
                      (hsame_refl provenance)
              | inr rest =>
                  cases rest with
                  | inl sameObserved =>
                      exact
                        And.intro (unary_transport observedUnary (hsame_symm sameObserved))
                          (hsame_refl provenance)
                  | inr rest =>
                      cases rest with
                      | inl sameMismatch =>
                          exact
                            And.intro
                              (unary_transport mismatchUnary (hsame_symm sameMismatch))
                              (hsame_refl provenance)
                      | inr rest =>
                          cases rest with
                          | inl sameReplay =>
                              exact
                                And.intro
                                  (unary_transport replayUnary (hsame_symm sameReplay))
                                  (hsame_refl provenance)
                          | inr sameRouted =>
                              exact
                                And.intro
                                  (unary_transport routedUnary (hsame_symm sameRouted))
                                  (hsame_refl provenance)
  }

end BEDC.Derived.ContinuationCountermodelUp
