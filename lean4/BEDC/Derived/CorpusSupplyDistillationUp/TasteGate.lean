import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CorpusSupplyDistillationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CorpusSupplyDistillationUp : Type where
  | mk :
      (corpus filtering distillation outputPrior refusal transport route provenance name : BHist) →
        CorpusSupplyDistillationUp
  deriving DecidableEq

private def corpusSupplyDistillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: corpusSupplyDistillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: corpusSupplyDistillationEncodeBHist h

private def corpusSupplyDistillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (corpusSupplyDistillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (corpusSupplyDistillationDecodeBHist tail)

private theorem corpusSupplyDistillationDecode_encode_bhist :
    ∀ h : BHist,
      corpusSupplyDistillationDecodeBHist (corpusSupplyDistillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem corpusSupplyDistillation_mk_congr
    {corpus corpus' filtering filtering' distillation distillation'
      outputPrior outputPrior' refusal refusal' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hCorpus : corpus' = corpus)
    (hFiltering : filtering' = filtering)
    (hDistillation : distillation' = distillation)
    (hOutputPrior : outputPrior' = outputPrior)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CorpusSupplyDistillationUp.mk corpus' filtering' distillation' outputPrior' refusal'
        transport' route' provenance' name' =
      CorpusSupplyDistillationUp.mk corpus filtering distillation outputPrior refusal transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCorpus
  cases hFiltering
  cases hDistillation
  cases hOutputPrior
  cases hRefusal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def corpusSupplyDistillationToEventFlow : CorpusSupplyDistillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CorpusSupplyDistillationUp.mk corpus filtering distillation outputPrior refusal transport
      route provenance name =>
      [[BMark.b0],
        corpusSupplyDistillationEncodeBHist corpus,
        [BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist filtering,
        [BMark.b1, BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist distillation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist outputPrior,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        corpusSupplyDistillationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        corpusSupplyDistillationEncodeBHist name]

private def corpusSupplyDistillationFromEventFlow :
    EventFlow → Option CorpusSupplyDistillationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | corpus :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | filtering :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | distillation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | outputPrior :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CorpusSupplyDistillationUp.mk
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    corpus)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    filtering)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    distillation)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    outputPrior)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    refusal)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    transport)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    route)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    provenance)
                                                                                  (corpusSupplyDistillationDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem corpusSupplyDistillation_round_trip :
    ∀ x : CorpusSupplyDistillationUp,
      corpusSupplyDistillationFromEventFlow (corpusSupplyDistillationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk corpus filtering distillation outputPrior refusal transport route provenance name =>
      change
        some
          (CorpusSupplyDistillationUp.mk
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist corpus))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist filtering))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist distillation))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist outputPrior))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist refusal))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist transport))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist route))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist provenance))
            (corpusSupplyDistillationDecodeBHist
              (corpusSupplyDistillationEncodeBHist name))) =
          some
            (CorpusSupplyDistillationUp.mk corpus filtering distillation outputPrior refusal
              transport route provenance name)
      exact
        congrArg some
          (corpusSupplyDistillation_mk_congr
            (corpusSupplyDistillationDecode_encode_bhist corpus)
            (corpusSupplyDistillationDecode_encode_bhist filtering)
            (corpusSupplyDistillationDecode_encode_bhist distillation)
            (corpusSupplyDistillationDecode_encode_bhist outputPrior)
            (corpusSupplyDistillationDecode_encode_bhist refusal)
            (corpusSupplyDistillationDecode_encode_bhist transport)
            (corpusSupplyDistillationDecode_encode_bhist route)
            (corpusSupplyDistillationDecode_encode_bhist provenance)
            (corpusSupplyDistillationDecode_encode_bhist name))

private theorem corpusSupplyDistillationToEventFlow_injective
    {x y : CorpusSupplyDistillationUp} :
    corpusSupplyDistillationToEventFlow x = corpusSupplyDistillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      corpusSupplyDistillationFromEventFlow (corpusSupplyDistillationToEventFlow x) =
        corpusSupplyDistillationFromEventFlow (corpusSupplyDistillationToEventFlow y) :=
    congrArg corpusSupplyDistillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (corpusSupplyDistillation_round_trip x).symm
      (Eq.trans hread (corpusSupplyDistillation_round_trip y)))

private def corpusSupplyDistillationFields : CorpusSupplyDistillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CorpusSupplyDistillationUp.mk corpus filtering distillation outputPrior refusal transport
      route provenance name =>
      [corpus, filtering, distillation, outputPrior, refusal, transport, route, provenance,
        name]

private theorem corpusSupplyDistillation_field_faithful :
    ∀ x y : CorpusSupplyDistillationUp,
      corpusSupplyDistillationFields x = corpusSupplyDistillationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk corpus₁ filtering₁ distillation₁ outputPrior₁ refusal₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk corpus₂ filtering₂ distillation₂ outputPrior₂ refusal₂ transport₂ route₂
          provenance₂ name₂ =>
          change
              [corpus₁, filtering₁, distillation₁, outputPrior₁, refusal₁, transport₁,
                route₁, provenance₁, name₁] =
                [corpus₂, filtering₂, distillation₂, outputPrior₂, refusal₂, transport₂,
                  route₂, provenance₂, name₂] at h
          injection h with hCorpus t1
          injection t1 with hFiltering t2
          injection t2 with hDistillation t3
          injection t3 with hOutputPrior t4
          injection t4 with hRefusal t5
          injection t5 with hTransport t6
          injection t6 with hRoute t7
          injection t7 with hProvenance t8
          injection t8 with hName _
          cases hCorpus
          cases hFiltering
          cases hDistillation
          cases hOutputPrior
          cases hRefusal
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance corpusSupplyDistillationBHistCarrier :
    BHistCarrier CorpusSupplyDistillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := corpusSupplyDistillationToEventFlow
  fromEventFlow := corpusSupplyDistillationFromEventFlow

instance corpusSupplyDistillationChapterTasteGate :
    ChapterTasteGate CorpusSupplyDistillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      corpusSupplyDistillationFromEventFlow
        (corpusSupplyDistillationToEventFlow x) = some x
    exact corpusSupplyDistillation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (corpusSupplyDistillationToEventFlow_injective heq)

instance corpusSupplyDistillationFieldFaithful :
    FieldFaithful CorpusSupplyDistillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := corpusSupplyDistillationFields
  field_faithful := corpusSupplyDistillation_field_faithful

instance corpusSupplyDistillationNontrivial :
    Nontrivial CorpusSupplyDistillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CorpusSupplyDistillationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CorpusSupplyDistillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CorpusSupplyDistillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  corpusSupplyDistillationChapterTasteGate

theorem CorpusSupplyDistillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      corpusSupplyDistillationDecodeBHist
        (corpusSupplyDistillationEncodeBHist h) = h) ∧
      (∀ x : CorpusSupplyDistillationUp,
        corpusSupplyDistillationFromEventFlow
          (corpusSupplyDistillationToEventFlow x) = some x) ∧
        (∀ x y : CorpusSupplyDistillationUp,
          corpusSupplyDistillationToEventFlow x =
            corpusSupplyDistillationToEventFlow y → x = y) ∧
          corpusSupplyDistillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨corpusSupplyDistillationDecode_encode_bhist, corpusSupplyDistillation_round_trip,
      (fun _ _ heq => corpusSupplyDistillationToEventFlow_injective heq), rfl⟩

theorem CorpusSupplyDistillationNameCert_obligations
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        hsame H H ∧ Cont T P (append T P) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F D O R H T P N =>
      exact ⟨C, F, D, O, R, H, T, P, N, rfl, hsame_refl H, rfl⟩

theorem CorpusSupplyDistillation_carried_output_boundary
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        Cont C F (append C F) ∧
          Cont F D (append F D) ∧
            Cont D O (append D O) ∧ hsame H H := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F D O R H T P N =>
      exact ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl, rfl, hsame_refl H⟩

theorem CorpusSupplyDistillationCarrier_admission
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            hsame H H ∧ Cont T P (append T P) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F D O R H T P N =>
      exact
        ⟨C, F, D, O, R, H, T, P, N, rfl, rfl,
          corpusSupplyDistillationChapterTasteGate.round_trip
            (CorpusSupplyDistillationUp.mk C F D O R H T P N),
          hsame_refl H, rfl⟩

theorem CorpusSupplyDistillation_public_nonescape {x : CorpusSupplyDistillationUp} :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        hsame H H ∧
          Cont T P (append T P) ∧
            (Cont (append T P) (BHist.e0 C) T → False) ∧
              (Cont (append T P) (BHist.e1 C) T → False) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F D O R H T P N =>
      exact
        ⟨C, F, D, O, R, H, T, P, N, rfl, hsame_refl H, rfl,
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := T) (k := append T P) (leftTail := P) (rightTail := C)).left rfl hbad),
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := T) (k := append T P) (leftTail := P) (rightTail := C)).right rfl hbad)⟩

theorem CorpusSupplyDistillation_output_prior_refusal_exactness
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        Cont O R (append O R) ∧
          Cont R N (append R N) ∧
            (Cont (append R N) (BHist.e0 O) R → False) ∧
              (Cont (append R N) (BHist.e1 O) R → False) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F D O R H T P N =>
      exact
        ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl,
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := R) (k := append R N) (leftTail := N) (rightTail := O)).left rfl hbad),
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := R) (k := append R N) (leftTail := N) (rightTail := O)).right rfl hbad)⟩

theorem CorpusSupplyDistillationSourceChannel_exposure :
    (∀ x : CorpusSupplyDistillationUp,
      ∃ C F D O R H T P N : BHist,
        x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
          FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N]) ∧
      (∀ F D O R H T P N : BHist,
        FieldFaithful.fields
            (CorpusSupplyDistillationUp.mk (BHist.e0 BHist.Empty) F D O R H T P N) ≠
          FieldFaithful.fields
            (CorpusSupplyDistillationUp.mk BHist.Empty F D O R H T P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk C F D O R H T P N =>
        exact ⟨C, F, D, O, R, H, T, P, N, rfl, rfl⟩
  · intro F D O R H T P N hfields
    change
      [BHist.e0 BHist.Empty, F, D, O, R, H, T, P, N] =
        [BHist.Empty, F, D, O, R, H, T, P, N] at hfields
    injection hfields with hrow _
    cases hrow

theorem CorpusSupplyDistillation_filter_route_order
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        Cont C F (append C F) ∧
          Cont F D (append F D) ∧
            Cont D O (append D O) ∧
              FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  cases x with
  | mk C F D O R H T P N =>
      exact ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl, rfl, rfl⟩

theorem CorpusSupplyDistillation_classifier_stability
    {x y : CorpusSupplyDistillationUp} :
    FieldFaithful.fields x = FieldFaithful.fields y →
      ∃ C F D O R H T P N : BHist,
        x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
          y = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
            FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N] ∧
              Cont C F (append C F) ∧
                Cont F D (append F D) ∧
                  Cont D O (append D O) ∧ Cont R N (append R N) := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields
  cases x with
  | mk C₁ F₁ D₁ O₁ R₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk C₂ F₂ D₂ O₂ R₂ H₂ T₂ P₂ N₂ =>
          change
              [C₁, F₁, D₁, O₁, R₁, H₁, T₁, P₁, N₁] =
                [C₂, F₂, D₂, O₂, R₂, H₂, T₂, P₂, N₂] at hfields
          injection hfields with hC t1
          injection t1 with hF t2
          injection t2 with hD t3
          injection t3 with hO t4
          injection t4 with hR t5
          injection t5 with hH t6
          injection t6 with hT t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hC
          cases hF
          cases hD
          cases hO
          cases hR
          cases hH
          cases hT
          cases hP
          cases hN
          exact
            ⟨C₁, F₁, D₁, O₁, R₁, H₁, T₁, P₁, N₁, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl⟩

theorem CorpusSupplyDistillation_refusal_exactness
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        Cont R H (append R H) ∧
          Cont H T (append H T) ∧
            Cont T P (append T P) ∧
              Cont P N (append P N) ∧
                (Cont (append P N) (BHist.e0 R) P → False) ∧
                  (Cont (append P N) (BHist.e1 R) P → False) := by
  -- BEDC touchpoint anchor: BHist Cont
  cases x with
  | mk C F D O R H T P N =>
      exact
        ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl, rfl, rfl,
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := P) (k := append P N) (leftTail := N) (rightTail := R)).left rfl hbad),
          (fun hbad =>
            (cont_mutual_extension_right_tail_absurd
              (h := P) (k := append P N) (leftTail := N) (rightTail := R)).right rfl hbad)⟩

theorem CorpusSupplyDistillationLedger_exactness
    (x : CorpusSupplyDistillationUp) :
    ∃ C F D O R H T P N : BHist,
      x = CorpusSupplyDistillationUp.mk C F D O R H T P N ∧
        FieldFaithful.fields x = [C, F, D, O, R, H, T, P, N] ∧
          Cont C F (append C F) ∧
            Cont F D (append F D) ∧
              Cont D O (append D O) ∧
                Cont R H (append R H) ∧
                  Cont H T (append H T) ∧
                    Cont T P (append T P) ∧ Cont P N (append P N) := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  cases x with
  | mk C F D O R H T P N =>
      exact ⟨C, F, D, O, R, H, T, P, N, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CorpusSupplyDistillationUp
