import BEDC.Derived.ClosurePreservationAuditWitnessUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ClosurePreservationAuditWitnessUp
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICClosurePreservationWitnessUp : Type where
  | mk (A T D L H C P N : BHist) : MetaCICClosurePreservationWitnessUp
  deriving DecidableEq

def metaCICClosurePreservationWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICClosurePreservationWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICClosurePreservationWitnessEncodeBHist h

def metaCICClosurePreservationWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICClosurePreservationWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICClosurePreservationWitnessDecodeBHist tail)

private theorem MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICClosurePreservationWitnessDecodeBHist
        (metaCICClosurePreservationWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICClosurePreservationWitnessFields :
    MetaCICClosurePreservationWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICClosurePreservationWitnessUp.mk A T D L H C P N =>
      [A, T, D, L, H, C, P, N]

def metaCICClosurePreservationWitnessToEventFlow :
    MetaCICClosurePreservationWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map metaCICClosurePreservationWitnessEncodeBHist
        (metaCICClosurePreservationWitnessFields x)

def metaCICClosurePreservationWitnessFromEventFlow
    (ef : EventFlow) : Option MetaCICClosurePreservationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | A :: restA =>
      match restA with
      | [] => none
      | T :: restT =>
          match restT with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | L :: restL =>
                  match restL with
                  | [] => none
                  | H :: restH =>
                      match restH with
                      | [] => none
                      | C :: restC =>
                          match restC with
                          | [] => none
                          | P :: restP =>
                              match restP with
                              | [] => none
                              | N :: restN =>
                                  match restN with
                                  | [] =>
                                      some
                                        (MetaCICClosurePreservationWitnessUp.mk
                                          (metaCICClosurePreservationWitnessDecodeBHist A)
                                          (metaCICClosurePreservationWitnessDecodeBHist T)
                                          (metaCICClosurePreservationWitnessDecodeBHist D)
                                          (metaCICClosurePreservationWitnessDecodeBHist L)
                                          (metaCICClosurePreservationWitnessDecodeBHist H)
                                          (metaCICClosurePreservationWitnessDecodeBHist C)
                                          (metaCICClosurePreservationWitnessDecodeBHist P)
                                          (metaCICClosurePreservationWitnessDecodeBHist N))
                                  | _ :: _ => none

private theorem MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICClosurePreservationWitnessUp,
      metaCICClosurePreservationWitnessFromEventFlow
        (metaCICClosurePreservationWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A T D L H C P N =>
      change
        some
          (MetaCICClosurePreservationWitnessUp.mk
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist A))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist T))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist D))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist L))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist H))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist C))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist P))
            (metaCICClosurePreservationWitnessDecodeBHist
              (metaCICClosurePreservationWitnessEncodeBHist N))) =
          some (MetaCICClosurePreservationWitnessUp.mk A T D L H C P N)
      rw [MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode A,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode T,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode D,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode L,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode H,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode C,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode P,
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_decode N]

private theorem MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_injective
    {x y : MetaCICClosurePreservationWitnessUp} :
    metaCICClosurePreservationWitnessToEventFlow x =
      metaCICClosurePreservationWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICClosurePreservationWitnessFromEventFlow
          (metaCICClosurePreservationWitnessToEventFlow x) =
        metaCICClosurePreservationWitnessFromEventFlow
          (metaCICClosurePreservationWitnessToEventFlow y) :=
    congrArg metaCICClosurePreservationWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance metaCICClosurePreservationWitnessBHistCarrier :
    BHistCarrier MetaCICClosurePreservationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICClosurePreservationWitnessToEventFlow
  fromEventFlow := metaCICClosurePreservationWitnessFromEventFlow

instance metaCICClosurePreservationWitnessChapterTasteGate :
    ChapterTasteGate MetaCICClosurePreservationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICClosurePreservationWitnessFromEventFlow
        (metaCICClosurePreservationWitnessToEventFlow x) = some x
    exact MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetaCICClosurePreservationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICClosurePreservationWitnessChapterTasteGate

theorem MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment :
    (forall x : MetaCICClosurePreservationWitnessUp,
      metaCICClosurePreservationWitnessFromEventFlow
        (metaCICClosurePreservationWitnessToEventFlow x) = some x) ∧
      (forall x y : MetaCICClosurePreservationWitnessUp,
        metaCICClosurePreservationWitnessToEventFlow x =
          metaCICClosurePreservationWitnessToEventFlow y -> x = y) ∧
        metaCICClosurePreservationWitnessFields
          (MetaCICClosurePreservationWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICClosurePreservationWitnessTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

theorem MetaCICClosurePreservationWitness_audit_substitution_handoff [AskSetup]
    [PackageSetup]
    {S V F B R H C P N substitutionRead fullSubstitutionRead
      A T D L Hwit Cwit Pwit Nwit witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg →
      Cont S V substitutionRead →
        Cont substitutionRead F fullSubstitutionRead →
          PkgSig bundle fullSubstitutionRead pkg →
            hsame A fullSubstitutionRead →
              UnaryHistory D →
                Cont A D witnessRead →
                  MetaCICClosurePreservationWitnessUp.mk A T D L Hwit Cwit Pwit Nwit =
                      MetaCICClosurePreservationWitnessUp.mk
                        fullSubstitutionRead T D L Hwit Cwit Pwit Nwit ∧
                    UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory witnessRead ∧
                      Cont S V substitutionRead ∧
                        Cont substitutionRead F fullSubstitutionRead ∧
                          Cont A D witnessRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle fullSubstitutionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier substitutionRoute fullSubstitutionRoute fullSubstitutionPkg auditSame dUnary
    witnessRoute
  obtain ⟨_sUnary, _vUnary, _fUnary, _substitutionUnary, fullSubstitutionUnary,
    substitutionRoute', fullSubstitutionRoute', provenancePkg, fullSubstitutionPkg'⟩ :=
      ClosurePreservationAuditWitness_substitution_row carrier substitutionRoute
        fullSubstitutionRoute fullSubstitutionPkg
  have auditUnary : UnaryHistory A :=
    unary_transport fullSubstitutionUnary (hsame_symm auditSame)
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed auditUnary dUnary witnessRoute
  constructor
  · cases auditSame
    rfl
  · exact
      ⟨auditUnary, dUnary, witnessUnary, substitutionRoute',
        fullSubstitutionRoute', witnessRoute, provenancePkg, fullSubstitutionPkg'⟩

theorem MetaCICClosurePreservationWitness_audit_beta_star_handoff [AskSetup]
    [PackageSetup]
    {S V F B R H C P N betaStarRead A T D L Hwit Cwit Pwit Nwit witnessRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg →
      Cont R N betaStarRead →
        PkgSig bundle betaStarRead pkg →
          hsame A betaStarRead →
            UnaryHistory D →
              Cont A D witnessRead →
                MetaCICClosurePreservationWitnessUp.mk A T D L Hwit Cwit Pwit Nwit =
                    MetaCICClosurePreservationWitnessUp.mk
                      betaStarRead T D L Hwit Cwit Pwit Nwit ∧
                  UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory witnessRead ∧
                    Cont B R C ∧ Cont R N betaStarRead ∧ Cont A D witnessRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle betaStarRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier betaStarRoute betaStarPkg auditSame dUnary witnessRoute
  obtain ⟨_bUnary, _rUnary, betaStarUnary, betaStepRoute, betaStarRoute',
    provenancePkg, betaStarPkg'⟩ :=
      ClosurePreservationAuditWitness_beta_star_row carrier betaStarRoute betaStarPkg
  have auditUnary : UnaryHistory A :=
    unary_transport betaStarUnary (hsame_symm auditSame)
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed auditUnary dUnary witnessRoute
  constructor
  · cases auditSame
    rfl
  · exact
      ⟨auditUnary, dUnary, witnessUnary, betaStepRoute, betaStarRoute',
        witnessRoute, provenancePkg, betaStarPkg'⟩

end BEDC.Derived.MetaCICClosurePreservationWitnessUp
