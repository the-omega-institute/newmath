import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalizationBudgetUp : Type where
  | mk (term candidate evidence normalization adequacy replay refusal transport routes
      provenance localName : BHist) : MetaCICNormalizationBudgetUp
  deriving DecidableEq

def metaCICNormalizationBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalizationBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalizationBudgetEncodeBHist h

def metaCICNormalizationBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalizationBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalizationBudgetDecodeBHist tail)

private theorem metaCICNormalizationBudgetDecode_encode_bhist :
    ∀ h : BHist,
      metaCICNormalizationBudgetDecodeBHist
        (metaCICNormalizationBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem metaCICNormalizationBudget_mk_congr
    {term term' candidate candidate' evidence evidence' normalization normalization'
      adequacy adequacy' replay replay' refusal refusal' transport transport'
      routes routes' provenance provenance' localName localName' : BHist}
    (hTerm : term' = term)
    (hCandidate : candidate' = candidate)
    (hEvidence : evidence' = evidence)
    (hNormalization : normalization' = normalization)
    (hAdequacy : adequacy' = adequacy)
    (hReplay : replay' = replay)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MetaCICNormalizationBudgetUp.mk term' candidate' evidence' normalization' adequacy'
        replay' refusal' transport' routes' provenance' localName' =
      MetaCICNormalizationBudgetUp.mk term candidate evidence normalization adequacy replay
        refusal transport routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTerm
  cases hCandidate
  cases hEvidence
  cases hNormalization
  cases hAdequacy
  cases hReplay
  cases hRefusal
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

def metaCICNormalizationBudgetToEventFlow : MetaCICNormalizationBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationBudgetUp.mk term candidate evidence normalization adequacy replay
      refusal transport routes provenance localName =>
      [[BMark.b0],
        metaCICNormalizationBudgetEncodeBHist term,
        [BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist candidate,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist evidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist normalization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist adequacy,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICNormalizationBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICNormalizationBudgetEncodeBHist localName]

def metaCICNormalizationBudgetFromEventFlow :
    EventFlow → Option MetaCICNormalizationBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | candidate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | evidence :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | normalization :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | adequacy :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | refusal :: rest13 =>
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
                                                                      | routes :: rest17 =>
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
                                                                                      | localName :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (MetaCICNormalizationBudgetUp.mk
                                                                                                  (metaCICNormalizationBudgetDecodeBHist term)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist candidate)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist evidence)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist normalization)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist adequacy)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist replay)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist refusal)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist transport)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist routes)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist provenance)
                                                                                                  (metaCICNormalizationBudgetDecodeBHist localName))
                                                                                          | _ :: _ => none

private theorem metaCICNormalizationBudget_round_trip :
    ∀ x : MetaCICNormalizationBudgetUp,
      metaCICNormalizationBudgetFromEventFlow
        (metaCICNormalizationBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term candidate evidence normalization adequacy replay refusal transport routes
      provenance localName =>
      change
        some
          (MetaCICNormalizationBudgetUp.mk
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist term))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist candidate))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist evidence))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist normalization))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist adequacy))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist replay))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist refusal))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist transport))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist routes))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist provenance))
            (metaCICNormalizationBudgetDecodeBHist
              (metaCICNormalizationBudgetEncodeBHist localName))) =
          some
            (MetaCICNormalizationBudgetUp.mk term candidate evidence normalization
              adequacy replay refusal transport routes provenance localName)
      exact
        congrArg some
          (metaCICNormalizationBudget_mk_congr
            (metaCICNormalizationBudgetDecode_encode_bhist term)
            (metaCICNormalizationBudgetDecode_encode_bhist candidate)
            (metaCICNormalizationBudgetDecode_encode_bhist evidence)
            (metaCICNormalizationBudgetDecode_encode_bhist normalization)
            (metaCICNormalizationBudgetDecode_encode_bhist adequacy)
            (metaCICNormalizationBudgetDecode_encode_bhist replay)
            (metaCICNormalizationBudgetDecode_encode_bhist refusal)
            (metaCICNormalizationBudgetDecode_encode_bhist transport)
            (metaCICNormalizationBudgetDecode_encode_bhist routes)
            (metaCICNormalizationBudgetDecode_encode_bhist provenance)
            (metaCICNormalizationBudgetDecode_encode_bhist localName))

private theorem metaCICNormalizationBudgetToEventFlow_injective
    {x y : MetaCICNormalizationBudgetUp} :
    metaCICNormalizationBudgetToEventFlow x =
      metaCICNormalizationBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalizationBudgetFromEventFlow
          (metaCICNormalizationBudgetToEventFlow x) =
        metaCICNormalizationBudgetFromEventFlow
          (metaCICNormalizationBudgetToEventFlow y) :=
    congrArg metaCICNormalizationBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICNormalizationBudget_round_trip x).symm
      (Eq.trans hread (metaCICNormalizationBudget_round_trip y)))

instance metaCICNormalizationBudgetBHistCarrier :
    BHistCarrier MetaCICNormalizationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalizationBudgetToEventFlow
  fromEventFlow := metaCICNormalizationBudgetFromEventFlow

instance metaCICNormalizationBudgetChapterTasteGate :
    ChapterTasteGate MetaCICNormalizationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalizationBudgetFromEventFlow
        (metaCICNormalizationBudgetToEventFlow x) = some x
    exact metaCICNormalizationBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICNormalizationBudgetToEventFlow_injective heq)

instance metaCICNormalizationBudgetFieldFaithful :
    FieldFaithful MetaCICNormalizationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICNormalizationBudgetUp.mk term candidate evidence normalization adequacy replay
        refusal transport routes provenance localName =>
        [term, candidate, evidence, normalization, adequacy, replay, refusal, transport,
          routes, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk term candidate evidence normalization adequacy replay refusal transport routes
        provenance localName =>
        cases y with
        | mk term' candidate' evidence' normalization' adequacy' replay' refusal'
            transport' routes' provenance' localName' =>
            cases hfields
            rfl

instance metaCICNormalizationBudgetNontrivial :
    Nontrivial MetaCICNormalizationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalizationBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICNormalizationBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICNormalizationBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICNormalizationBudgetChapterTasteGate

theorem MetaCICNormalizationBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalizationBudgetDecodeBHist
        (metaCICNormalizationBudgetEncodeBHist h) = h) ∧
      (∀ x : MetaCICNormalizationBudgetUp,
        metaCICNormalizationBudgetFromEventFlow
          (metaCICNormalizationBudgetToEventFlow x) = some x) ∧
        (∀ x y : MetaCICNormalizationBudgetUp,
          metaCICNormalizationBudgetToEventFlow x =
            metaCICNormalizationBudgetToEventFlow y → x = y) ∧
          metaCICNormalizationBudgetEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : MetaCICNormalizationBudgetUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICNormalizationBudgetDecode_encode_bhist
  · constructor
    · exact metaCICNormalizationBudget_round_trip
    · constructor
      · intro x y heq
        exact metaCICNormalizationBudgetToEventFlow_injective heq
      · constructor
        · rfl
        · exact
            ⟨MetaCICNormalizationBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              MetaCICNormalizationBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
