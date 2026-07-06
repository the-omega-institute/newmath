import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Sig
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NontrivialZeroClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Bundle
open BEDC.FKernel.Sig
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NontrivialZeroClassifierUp : Type where
  | mk :
      (zero strip witness trivial realPart comparison transport route provenance name : BHist) →
        NontrivialZeroClassifierUp
  deriving DecidableEq

private def nontrivialZeroClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nontrivialZeroClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nontrivialZeroClassifierEncodeBHist h

private def nontrivialZeroClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nontrivialZeroClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nontrivialZeroClassifierDecodeBHist tail)

private theorem nontrivialZeroClassifierDecodeEncodeBHist :
    ∀ h : BHist,
      nontrivialZeroClassifierDecodeBHist (nontrivialZeroClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def nontrivialZeroClassifierToEventFlow : NontrivialZeroClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NontrivialZeroClassifierUp.mk zero strip witness trivial realPart comparison transport route
      provenance name =>
      [[BMark.b0],
        nontrivialZeroClassifierEncodeBHist zero,
        [BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist strip,
        [BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist trivial,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist realPart,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nontrivialZeroClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        nontrivialZeroClassifierEncodeBHist name]

private def nontrivialZeroClassifierFromEventFlow :
    EventFlow → Option NontrivialZeroClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | zero :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | strip :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | witness :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | trivial :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realPart :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | comparison :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (NontrivialZeroClassifierUp.mk
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            zero)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            strip)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            witness)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            trivial)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            realPart)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            comparison)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            transport)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            route)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            provenance)
                                                                                          (nontrivialZeroClassifierDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem nontrivialZeroClassifierRoundTrip :
    ∀ x : NontrivialZeroClassifierUp,
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk zero strip witness trivial realPart comparison transport route provenance name =>
      change
        some
          (NontrivialZeroClassifierUp.mk
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist zero))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist strip))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist witness))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist trivial))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist realPart))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist comparison))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist transport))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist route))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist provenance))
            (nontrivialZeroClassifierDecodeBHist
              (nontrivialZeroClassifierEncodeBHist name))) =
          some
            (NontrivialZeroClassifierUp.mk zero strip witness trivial realPart comparison
              transport route provenance name)
      rw [nontrivialZeroClassifierDecodeEncodeBHist zero,
        nontrivialZeroClassifierDecodeEncodeBHist strip,
        nontrivialZeroClassifierDecodeEncodeBHist witness,
        nontrivialZeroClassifierDecodeEncodeBHist trivial,
        nontrivialZeroClassifierDecodeEncodeBHist realPart,
        nontrivialZeroClassifierDecodeEncodeBHist comparison,
        nontrivialZeroClassifierDecodeEncodeBHist transport,
        nontrivialZeroClassifierDecodeEncodeBHist route,
        nontrivialZeroClassifierDecodeEncodeBHist provenance,
        nontrivialZeroClassifierDecodeEncodeBHist name]

private theorem nontrivialZeroClassifierToEventFlow_injective
    {x y : NontrivialZeroClassifierUp} :
    nontrivialZeroClassifierToEventFlow x = nontrivialZeroClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) =
        nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow y) :=
    congrArg nontrivialZeroClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nontrivialZeroClassifierRoundTrip x).symm
      (Eq.trans hread (nontrivialZeroClassifierRoundTrip y)))

def nontrivialZeroClassifierFields : NontrivialZeroClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NontrivialZeroClassifierUp.mk zero strip witness trivial realPart comparison transport route
      provenance name =>
      [zero, strip, witness, trivial, realPart, comparison, transport, route, provenance,
        name]

private theorem nontrivialZeroClassifier_field_faithful :
    ∀ x y : NontrivialZeroClassifierUp,
      nontrivialZeroClassifierFields x = nontrivialZeroClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk zero strip witness trivial realPart comparison transport route provenance name =>
      cases y with
      | mk zero' strip' witness' trivial' realPart' comparison' transport' route'
          provenance' name' =>
          cases hfields
          rfl

instance nontrivialZeroClassifierBHistCarrier : BHistCarrier NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nontrivialZeroClassifierToEventFlow
  fromEventFlow := nontrivialZeroClassifierFromEventFlow

instance nontrivialZeroClassifierChapterTasteGate :
    ChapterTasteGate NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nontrivialZeroClassifierFromEventFlow (nontrivialZeroClassifierToEventFlow x) = some x
    exact nontrivialZeroClassifierRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nontrivialZeroClassifierToEventFlow_injective heq)

instance nontrivialZeroClassifierFieldFaithful :
    FieldFaithful NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nontrivialZeroClassifierFields
  field_faithful := nontrivialZeroClassifier_field_faithful

instance nontrivialZeroClassifierNontrivial : Nontrivial NontrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NontrivialZeroClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NontrivialZeroClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NontrivialZeroClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nontrivialZeroClassifierChapterTasteGate

theorem NontrivialZeroClassifierCarrier_critical_strip_handoff
    {zero strip witness route provenance name : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row zero ∨ hsame row strip ∨ hsame row witness ∨ hsame row route ∨
          hsame row provenance ∨ hsame row name)
      (fun row : BHist =>
        hsame row zero ∨ hsame row strip ∨ hsame row witness ∨ hsame row route ∨
          hsame row provenance ∨ hsame row name)
      (fun row : BHist =>
        hsame row zero ∨ hsame row strip ∨ hsame row witness ∨ hsame row route ∨
          hsame row provenance ∨ hsame row name)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame
  have sourceZero :
      (fun row : BHist =>
        hsame row zero ∨ hsame row strip ∨ hsame row witness ∨ hsame row route ∨
          hsame row provenance ∨ hsame row name) zero := by
    exact Or.inl (hsame_refl zero)
  exact {
    core := {
      carrier_inhabited := Exists.intro zero sourceZero
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _col same
        exact hsame_symm same
      equiv_trans := by
        intro _row _mid _col sameRowMid sameMidCol
        exact hsame_trans sameRowMid sameMidCol
      carrier_respects_equiv := by
        intro row col same source
        cases source with
        | inl rowZero =>
            exact Or.inl (hsame_trans (hsame_symm same) rowZero)
        | inr rest =>
            cases rest with
            | inl rowStrip =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowStrip))
            | inr rest =>
                cases rest with
                | inl rowWitness =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowWitness)))
                | inr rest =>
                    cases rest with
                    | inl rowRoute =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowRoute))))
                    | inr rest =>
                        cases rest with
                        | inl rowProvenance =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm same) rowProvenance)))))
                        | inr rowName =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (hsame_trans (hsame_symm same) rowName)))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NontrivialZeroClassifier_trivial_zero_exclusion_ledger [AskSetup]
    {bundle : ProbeBundle ProbeName} {critical trivial evidence : BHist} :
    SigRel bundle critical evidence ->
      hsame trivial BHist.Empty ->
        SemanticNameCert
          (fun row : BHist => hsame row evidence ∧ SigRel bundle critical evidence)
          (fun row : BHist =>
            hsame row critical ∨ hsame row trivial ∨ hsame row evidence)
          (fun row : BHist =>
            SigRel bundle critical evidence ∧ hsame trivial BHist.Empty)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle SigRel SemanticNameCert hsame
  intro criticalEvidence trivialEmpty
  have sourceEvidence :
      (fun row : BHist => hsame row evidence ∧ SigRel bundle critical evidence)
        evidence := by
    exact ⟨hsame_refl evidence, criticalEvidence⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro evidence sourceEvidence
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, trivialEmpty⟩
  }

end BEDC.Derived.NontrivialZeroClassifierUp
