import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OracleAugmentedSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OracleAugmentedSubstrateUp : Type where
  | mk :
      (substrate oracleCall transcript openBoundary quadrantEvidence transport route provenance
        nameCert : BHist) →
      OracleAugmentedSubstrateUp
  deriving DecidableEq

def oracleAugmentedSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oracleAugmentedSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oracleAugmentedSubstrateEncodeBHist h

def oracleAugmentedSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oracleAugmentedSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oracleAugmentedSubstrateDecodeBHist tail)

private theorem oracleAugmentedSubstrateDecode_encode_bhist :
    ∀ h : BHist,
      oracleAugmentedSubstrateDecodeBHist
        (oracleAugmentedSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def oracleAugmentedSubstrateFields : OracleAugmentedSubstrateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OracleAugmentedSubstrateUp.mk substrate oracleCall transcript openBoundary
      quadrantEvidence transport route provenance nameCert =>
      [substrate, oracleCall, transcript, openBoundary, quadrantEvidence, transport, route,
        provenance, nameCert]

def oracleAugmentedSubstrateToEventFlow : OracleAugmentedSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OracleAugmentedSubstrateUp.mk substrate oracleCall transcript openBoundary
      quadrantEvidence transport route provenance nameCert =>
      [[BMark.b0],
        oracleAugmentedSubstrateEncodeBHist substrate,
        [BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist oracleCall,
        [BMark.b1, BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist transcript,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist openBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist quadrantEvidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        oracleAugmentedSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        oracleAugmentedSubstrateEncodeBHist nameCert]

def oracleAugmentedSubstrateFromEventFlow :
    EventFlow → Option OracleAugmentedSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | substrate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | oracleCall :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transcript :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | openBoundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | quadrantEvidence :: rest9 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (OracleAugmentedSubstrateUp.mk
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    substrate)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    oracleCall)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    transcript)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    openBoundary)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    quadrantEvidence)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    transport)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    route)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    provenance)
                                                                                  (oracleAugmentedSubstrateDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem oracleAugmentedSubstrate_round_trip :
    ∀ x : OracleAugmentedSubstrateUp,
      oracleAugmentedSubstrateFromEventFlow
        (oracleAugmentedSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk substrate oracleCall transcript openBoundary quadrantEvidence transport route provenance
      nameCert =>
      change
        some
          (OracleAugmentedSubstrateUp.mk
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist substrate))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist oracleCall))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist transcript))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist openBoundary))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist quadrantEvidence))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist transport))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist route))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist provenance))
            (oracleAugmentedSubstrateDecodeBHist
              (oracleAugmentedSubstrateEncodeBHist nameCert))) =
          some
            (OracleAugmentedSubstrateUp.mk substrate oracleCall transcript openBoundary
              quadrantEvidence transport route provenance nameCert)
      rw [oracleAugmentedSubstrateDecode_encode_bhist substrate,
        oracleAugmentedSubstrateDecode_encode_bhist oracleCall,
        oracleAugmentedSubstrateDecode_encode_bhist transcript,
        oracleAugmentedSubstrateDecode_encode_bhist openBoundary,
        oracleAugmentedSubstrateDecode_encode_bhist quadrantEvidence,
        oracleAugmentedSubstrateDecode_encode_bhist transport,
        oracleAugmentedSubstrateDecode_encode_bhist route,
        oracleAugmentedSubstrateDecode_encode_bhist provenance,
        oracleAugmentedSubstrateDecode_encode_bhist nameCert]

private theorem oracleAugmentedSubstrateToEventFlow_injective
    {x y : OracleAugmentedSubstrateUp} :
    oracleAugmentedSubstrateToEventFlow x =
      oracleAugmentedSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oracleAugmentedSubstrateFromEventFlow
          (oracleAugmentedSubstrateToEventFlow x) =
        oracleAugmentedSubstrateFromEventFlow
          (oracleAugmentedSubstrateToEventFlow y) :=
    congrArg oracleAugmentedSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (oracleAugmentedSubstrate_round_trip x).symm
      (Eq.trans hread (oracleAugmentedSubstrate_round_trip y)))

private theorem oracleAugmentedSubstrate_fields_faithful :
    ∀ x y : OracleAugmentedSubstrateUp,
      oracleAugmentedSubstrateFields x = oracleAugmentedSubstrateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk substrate₁ oracleCall₁ transcript₁ openBoundary₁ quadrantEvidence₁ transport₁ route₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk substrate₂ oracleCall₂ transcript₂ openBoundary₂ quadrantEvidence₂ transport₂ route₂
          provenance₂ nameCert₂ =>
          simp only [oracleAugmentedSubstrateFields] at h
          cases h
          rfl

instance oracleAugmentedSubstrateBHistCarrier :
    BHistCarrier OracleAugmentedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oracleAugmentedSubstrateToEventFlow
  fromEventFlow := oracleAugmentedSubstrateFromEventFlow

instance oracleAugmentedSubstrateChapterTasteGate :
    ChapterTasteGate OracleAugmentedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      oracleAugmentedSubstrateFromEventFlow
        (oracleAugmentedSubstrateToEventFlow x) = some x
    exact oracleAugmentedSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (oracleAugmentedSubstrateToEventFlow_injective heq)

instance oracleAugmentedSubstrateFieldFaithful :
    FieldFaithful OracleAugmentedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := oracleAugmentedSubstrateFields
  field_faithful := oracleAugmentedSubstrate_fields_faithful

instance oracleAugmentedSubstrateNontrivial :
    Nontrivial OracleAugmentedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OracleAugmentedSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OracleAugmentedSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OracleAugmentedSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oracleAugmentedSubstrateChapterTasteGate

theorem OracleAugmentedSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      oracleAugmentedSubstrateDecodeBHist (oracleAugmentedSubstrateEncodeBHist h) = h) ∧
      (∀ x : OracleAugmentedSubstrateUp,
        oracleAugmentedSubstrateFromEventFlow
          (oracleAugmentedSubstrateToEventFlow x) = some x) ∧
        (∀ x y : OracleAugmentedSubstrateUp,
          oracleAugmentedSubstrateToEventFlow x =
            oracleAugmentedSubstrateToEventFlow y → x = y) ∧
          oracleAugmentedSubstrateEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : OracleAugmentedSubstrateUp,
              oracleAugmentedSubstrateFields x = oracleAugmentedSubstrateFields y → x = y) ∧
              (∃ x y : OracleAugmentedSubstrateUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact oracleAugmentedSubstrateDecode_encode_bhist
  · constructor
    · exact oracleAugmentedSubstrate_round_trip
    · constructor
      · intro x y heq
        exact oracleAugmentedSubstrateToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact oracleAugmentedSubstrate_fields_faithful
          · exact
              ⟨OracleAugmentedSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                OracleAugmentedSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.OracleAugmentedSubstrateUp
