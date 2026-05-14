import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SolipsismGapRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SolipsismGapRefusalUp : Type where
  | mk (evidence refusal residue transport route provenance nameCert : BHist) :
      SolipsismGapRefusalUp
  deriving DecidableEq

private def solipsismGapRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: solipsismGapRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: solipsismGapRefusalEncodeBHist h

private def solipsismGapRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (solipsismGapRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (solipsismGapRefusalDecodeBHist tail)

private theorem solipsismGapRefusalDecode_encode_bhist :
    ∀ h : BHist,
      solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def solipsismGapRefusalToEventFlow : SolipsismGapRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SolipsismGapRefusalUp.mk evidence refusal residue transport route provenance nameCert =>
      [[BMark.b0],
        solipsismGapRefusalEncodeBHist evidence,
        [BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist nameCert]

private def solipsismGapRefusalFromEventFlow : EventFlow → Option SolipsismGapRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | evidence :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | residue :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (SolipsismGapRefusalUp.mk
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    evidence)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    refusal)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    residue)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    transport)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    route)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    provenance)
                                                                  (solipsismGapRefusalDecodeBHist
                                                                    nameCert))
                                                          | _ :: _ => none

private theorem solipsismGapRefusal_round_trip :
    ∀ x : SolipsismGapRefusalUp,
      solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk evidence refusal residue transport route provenance nameCert =>
      change
        some
          (SolipsismGapRefusalUp.mk
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist evidence))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist refusal))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist residue))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist transport))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist route))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist provenance))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist nameCert))) =
          some
            (SolipsismGapRefusalUp.mk evidence refusal residue transport route provenance
              nameCert)
      rw [solipsismGapRefusalDecode_encode_bhist evidence,
        solipsismGapRefusalDecode_encode_bhist refusal,
        solipsismGapRefusalDecode_encode_bhist residue,
        solipsismGapRefusalDecode_encode_bhist transport,
        solipsismGapRefusalDecode_encode_bhist route,
        solipsismGapRefusalDecode_encode_bhist provenance,
        solipsismGapRefusalDecode_encode_bhist nameCert]

private theorem solipsismGapRefusalToEventFlow_injective
    {x y : SolipsismGapRefusalUp} :
    solipsismGapRefusalToEventFlow x = solipsismGapRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) =
        solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow y) :=
    congrArg solipsismGapRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (solipsismGapRefusal_round_trip x).symm
      (Eq.trans hread (solipsismGapRefusal_round_trip y)))

instance solipsismGapRefusalBHistCarrier : BHistCarrier SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := solipsismGapRefusalToEventFlow
  fromEventFlow := solipsismGapRefusalFromEventFlow

instance solipsismGapRefusalChapterTasteGate :
    ChapterTasteGate SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x
    exact solipsismGapRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (solipsismGapRefusalToEventFlow_injective heq)

instance solipsismGapRefusalFieldFaithful : FieldFaithful SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SolipsismGapRefusalUp.mk evidence refusal residue transport route provenance nameCert =>
        [evidence, refusal, residue, transport, route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk evidence₁ refusal₁ residue₁ transport₁ route₁ provenance₁ nameCert₁ =>
        cases y with
        | mk evidence₂ refusal₂ residue₂ transport₂ route₂ provenance₂ nameCert₂ =>
            injection h with hevidence t1
            injection t1 with hrefusal t2
            injection t2 with hresidue t3
            injection t3 with htransport t4
            injection t4 with hroute t5
            injection t5 with hprovenance t6
            injection t6 with hnameCert _
            cases hevidence
            cases hrefusal
            cases hresidue
            cases htransport
            cases hroute
            cases hprovenance
            cases hnameCert
            rfl

instance solipsismGapRefusalNontrivial : Nontrivial SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SolipsismGapRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SolipsismGapRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SolipsismGapRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  solipsismGapRefusalChapterTasteGate

theorem SolipsismGapRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist h) = h) ∧
      (∀ x : SolipsismGapRefusalUp,
        solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x) ∧
        (∀ x y : SolipsismGapRefusalUp,
          solipsismGapRefusalToEventFlow x = solipsismGapRefusalToEventFlow y → x = y) ∧
          solipsismGapRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact solipsismGapRefusalDecode_encode_bhist
  · constructor
    · exact solipsismGapRefusal_round_trip
    · constructor
      · intro x y heq
        exact solipsismGapRefusalToEventFlow_injective heq
      · rfl

end BEDC.Derived.SolipsismGapRefusalUp
