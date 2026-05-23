import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyConvergenceCriterionUp : Type where
  | mk : (S M D R E H C P N : BHist) → CauchyConvergenceCriterionUp

def cauchyConvergenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyConvergenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyConvergenceCriterionEncodeBHist h

def cauchyConvergenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyConvergenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyConvergenceCriterionDecodeBHist tail)

private theorem cauchyConvergenceCriterion_decode_encode_bhist :
    ∀ h : BHist,
      cauchyConvergenceCriterionDecodeBHist
          (cauchyConvergenceCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyConvergenceCriterionFields :
    CauchyConvergenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyConvergenceCriterionUp.mk S M D R E H C P N => [S, M, D, R, E, H, C, P, N]

def cauchyConvergenceCriterionToEventFlow :
    CauchyConvergenceCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyConvergenceCriterionUp.mk S M D R E H C P N =>
      cauchyConvergenceCriterionEncodeBHist S ::
        cauchyConvergenceCriterionEncodeBHist M ::
          cauchyConvergenceCriterionEncodeBHist D ::
            cauchyConvergenceCriterionEncodeBHist R ::
              cauchyConvergenceCriterionEncodeBHist E ::
                cauchyConvergenceCriterionEncodeBHist H ::
                  cauchyConvergenceCriterionEncodeBHist C ::
                    cauchyConvergenceCriterionEncodeBHist P ::
                      cauchyConvergenceCriterionEncodeBHist N :: []

def cauchyConvergenceCriterionFromEventFlow :
    EventFlow → Option CauchyConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    match flow with
    | [] => none
    | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CauchyConvergenceCriterionUp.mk
                                              (cauchyConvergenceCriterionDecodeBHist S)
                                              (cauchyConvergenceCriterionDecodeBHist M)
                                              (cauchyConvergenceCriterionDecodeBHist D)
                                              (cauchyConvergenceCriterionDecodeBHist R)
                                              (cauchyConvergenceCriterionDecodeBHist E)
                                              (cauchyConvergenceCriterionDecodeBHist H)
                                              (cauchyConvergenceCriterionDecodeBHist C)
                                              (cauchyConvergenceCriterionDecodeBHist P)
                                              (cauchyConvergenceCriterionDecodeBHist N))
                                      | _ :: _ => none

private theorem cauchyConvergenceCriterion_round_trip :
    ∀ x : CauchyConvergenceCriterionUp,
      cauchyConvergenceCriterionFromEventFlow
          (cauchyConvergenceCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D R E H C P N =>
      change
        some
          (CauchyConvergenceCriterionUp.mk
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist S))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist M))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist D))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist R))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist E))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist H))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist C))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist P))
            (cauchyConvergenceCriterionDecodeBHist
              (cauchyConvergenceCriterionEncodeBHist N))) =
          some (CauchyConvergenceCriterionUp.mk S M D R E H C P N)
      rw [cauchyConvergenceCriterion_decode_encode_bhist S,
        cauchyConvergenceCriterion_decode_encode_bhist M,
        cauchyConvergenceCriterion_decode_encode_bhist D,
        cauchyConvergenceCriterion_decode_encode_bhist R,
        cauchyConvergenceCriterion_decode_encode_bhist E,
        cauchyConvergenceCriterion_decode_encode_bhist H,
        cauchyConvergenceCriterion_decode_encode_bhist C,
        cauchyConvergenceCriterion_decode_encode_bhist P,
        cauchyConvergenceCriterion_decode_encode_bhist N]

private theorem cauchyConvergenceCriterionToEventFlow_injective
    {x y : CauchyConvergenceCriterionUp} :
    cauchyConvergenceCriterionToEventFlow x =
        cauchyConvergenceCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyConvergenceCriterionFromEventFlow
          (cauchyConvergenceCriterionToEventFlow x) =
        cauchyConvergenceCriterionFromEventFlow
          (cauchyConvergenceCriterionToEventFlow y) :=
    congrArg cauchyConvergenceCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyConvergenceCriterion_round_trip x).symm
      (Eq.trans hread (cauchyConvergenceCriterion_round_trip y)))

private theorem cauchyConvergenceCriterion_field_faithful :
    ∀ x y : CauchyConvergenceCriterionUp,
      cauchyConvergenceCriterionFields x = cauchyConvergenceCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance cauchyConvergenceCriterionBHistCarrier :
    BHistCarrier CauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyConvergenceCriterionToEventFlow
  fromEventFlow := cauchyConvergenceCriterionFromEventFlow

instance cauchyConvergenceCriterionChapterTasteGate :
    ChapterTasteGate CauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyConvergenceCriterionFromEventFlow
          (cauchyConvergenceCriterionToEventFlow x) =
        some x
    exact cauchyConvergenceCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyConvergenceCriterionToEventFlow_injective heq)

instance cauchyConvergenceCriterionFieldFaithful :
    FieldFaithful CauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyConvergenceCriterionFields
  field_faithful := cauchyConvergenceCriterion_field_faithful

instance cauchyConvergenceCriterionNontrivial :
    Nontrivial CauchyConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyConvergenceCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyConvergenceCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyConvergenceCriterionChapterTasteGate

theorem CauchyConvergenceCriterionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyConvergenceCriterionDecodeBHist
          (cauchyConvergenceCriterionEncodeBHist h) =
        h) /\
      (forall x : CauchyConvergenceCriterionUp,
        cauchyConvergenceCriterionFromEventFlow
            (cauchyConvergenceCriterionToEventFlow x) =
          some x) /\
        (forall x y : CauchyConvergenceCriterionUp,
          cauchyConvergenceCriterionToEventFlow x =
              cauchyConvergenceCriterionToEventFlow y ->
            x = y) /\
          cauchyConvergenceCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyConvergenceCriterion_decode_encode_bhist,
      cauchyConvergenceCriterion_round_trip,
      (fun _ _ heq => cauchyConvergenceCriterionToEventFlow_injective heq),
      rfl⟩

def CauchyConvergenceCriterionCarrier [AskSetup] [PackageSetup]
    (schedule modulus dyadic handoff sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory transportRow ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont schedule modulus dyadic ∧ Cont dyadic handoff sealRow ∧
          Cont sealRow transportRow route ∧ Cont route provenance localCert ∧
            hsame sealRow handoff ∧ hsame sealRow provenance ∧
              PkgSig bundle provenance pkg

theorem CauchyConvergenceCriterionCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow
              transportRow route provenance localCert bundle pkg ∧
            hsame row sealRow)
        (fun row : BHist =>
          CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow
              transportRow route provenance localCert bundle pkg ∧
            hsame row handoff)
        (fun row : BHist =>
          CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow
              transportRow route provenance localCert bundle pkg ∧
            hsame row provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert NameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
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
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      obtain ⟨carrierRows, sameRowSeal⟩ := source
      have carrierRowsCopy := carrierRows
      obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _handoffUnary, _sealUnary,
        _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
        _scheduleModulusDyadic, _dyadicHandoffSeal, _sealTransportRoute,
        _routeProvenanceLocal, sameSealHandoff, _sameSealProvenance,
        _provenancePkg⟩ := carrierRows
      exact And.intro carrierRowsCopy (hsame_trans sameRowSeal sameSealHandoff)
    ledger_sound := by
      intro _row source
      obtain ⟨carrierRows, sameRowSeal⟩ := source
      have carrierRowsCopy := carrierRows
      obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _handoffUnary, _sealUnary,
        _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
        _scheduleModulusDyadic, _dyadicHandoffSeal, _sealTransportRoute,
        _routeProvenanceLocal, _sameSealHandoff, sameSealProvenance,
        _provenancePkg⟩ := carrierRows
      exact And.intro carrierRowsCopy (hsame_trans sameRowSeal sameSealProvenance)
  }

end BEDC.Derived.CauchyConvergenceCriterionUp
