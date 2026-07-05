import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosurePreservationAuditWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosurePreservationAuditWitnessCarrier [AskSetup] [PackageSetup]
    (S V F B R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory F ∧ UnaryHistory B ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S V F ∧ Cont F B H ∧ Cont B R C ∧
        PkgSig bundle P pkg

theorem ClosurePreservationAuditWitness_beta_star_row [AskSetup] [PackageSetup]
    {S V F B R H C P N betaStarRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg →
      Cont R N betaStarRead →
        PkgSig bundle betaStarRead pkg →
          UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory betaStarRead ∧ Cont B R C ∧
            Cont R N betaStarRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle betaStarRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier betaStarRoute betaStarPkg
  obtain ⟨_sUnary, _vUnary, _fUnary, bUnary, rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _shiftVariableFull, _fullBetaTransport, betaStepRoute, provenancePkg⟩ :=
    carrier
  have betaStarUnary : UnaryHistory betaStarRead :=
    unary_cont_closed rUnary nUnary betaStarRoute
  exact
    ⟨bUnary, rUnary, betaStarUnary, betaStepRoute, betaStarRoute, provenancePkg,
      betaStarPkg⟩

theorem ClosurePreservationAuditWitness_substitution_row [AskSetup] [PackageSetup]
    {S V F B R H C P N substitutionRead fullSubstitutionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg →
      Cont S V substitutionRead →
        Cont substitutionRead F fullSubstitutionRead →
          PkgSig bundle fullSubstitutionRead pkg →
            UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory F ∧
              UnaryHistory substitutionRead ∧ UnaryHistory fullSubstitutionRead ∧
                Cont S V substitutionRead ∧ Cont substitutionRead F fullSubstitutionRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle fullSubstitutionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier substitutionRoute fullSubstitutionRoute fullSubstitutionPkg
  obtain ⟨sUnary, vUnary, fUnary, _bUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _shiftVariableFull, _fullBetaTransport, _betaStepRoute, provenancePkg⟩ :=
    carrier
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed sUnary vUnary substitutionRoute
  have fullSubstitutionUnary : UnaryHistory fullSubstitutionRead :=
    unary_cont_closed substitutionUnary fUnary fullSubstitutionRoute
  exact
    ⟨sUnary, vUnary, fUnary, substitutionUnary, fullSubstitutionUnary,
      substitutionRoute, fullSubstitutionRoute, provenancePkg, fullSubstitutionPkg⟩

theorem ClosurePreservationAuditWitness_beta_step_row [AskSetup] [PackageSetup]
    {S V F B R H C P N betaStepRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg →
      Cont B N betaStepRead →
        PkgSig bundle betaStepRead pkg →
          UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory F ∧ UnaryHistory B ∧
            UnaryHistory betaStepRead ∧ Cont S V F ∧ Cont F B H ∧
              Cont B N betaStepRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle betaStepRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier betaStepRoute betaStepPkg
  obtain ⟨sUnary, vUnary, fUnary, bUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, shiftVariableRoute, fullBetaRoute, _betaStepCarrierRoute, provenancePkg⟩ :=
    carrier
  have betaStepUnary : UnaryHistory betaStepRead :=
    unary_cont_closed bUnary nUnary betaStepRoute
  exact
    ⟨sUnary, vUnary, fUnary, bUnary, betaStepUnary, shiftVariableRoute, fullBetaRoute,
      betaStepRoute, provenancePkg, betaStepPkg⟩

theorem ClosurePreservationAuditWitness_namecert_obligations [AskSetup] [PackageSetup]
    {S V F B R H C P N nameRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier S V F B R H C P N bundle pkg ->
      Cont H C nameRead ->
        PkgSig bundle N pkg ->
          UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory F ∧ UnaryHistory B ∧
            UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
              UnaryHistory N ∧ UnaryHistory nameRead ∧ Cont S V F ∧ Cont F B H ∧
                Cont B R C ∧ Cont H C nameRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier nameRoute namePkg
  obtain ⟨sUnary, vUnary, fUnary, bUnary, rUnary, hUnary, cUnary, pUnary, nUnary,
    shiftVariableRoute, fullBetaRoute, betaStepRoute, provenancePkg⟩ := carrier
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed hUnary cUnary nameRoute
  exact
    ⟨sUnary, vUnary, fUnary, bUnary, rUnary, hUnary, cUnary, pUnary, nUnary, nameUnary,
      shiftVariableRoute, fullBetaRoute, betaStepRoute, nameRoute, provenancePkg, namePkg⟩

theorem ClosurePreservationAuditWitness_non_escape [AskSetup] [PackageSetup]
    {source value frontier betaStep betaStar history certificate provenance name betaRead
      substRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosurePreservationAuditWitnessCarrier source value frontier betaStep betaStar history
        certificate provenance name bundle pkg ->
      Cont betaStep betaStar betaRead ->
        Cont frontier value substRead ->
          SemanticNameCert
              (fun row : BHist => hsame row name /\ UnaryHistory row)
              (fun row : BHist =>
                hsame row source \/ hsame row value \/ hsame row frontier \/
                  hsame row betaStep \/ hsame row betaStar \/ hsame row history \/
                    hsame row certificate \/ hsame row provenance \/ hsame row name)
              (fun row : BHist => hsame row name /\ Cont betaStep betaStar betaRead /\
                Cont frontier value substRead)
              hsame /\ UnaryHistory betaRead /\ UnaryHistory substRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier betaRoute substRoute
  obtain ⟨sourceUnary, valueUnary, frontierUnary, betaStepUnary, betaStarUnary, historyUnary,
    _certificateUnary, _provenanceUnary, nameUnary, _sourceValueFrontier,
    _frontierBetaHistory, _betaStepRoute, _provenancePkg⟩ := carrier
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaStepUnary betaStarUnary betaRoute
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed frontierUnary valueUnary substRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row source \/ hsame row value \/ hsame row frontier \/
              hsame row betaStep \/ hsame row betaStar \/ hsame row history \/
                hsame row certificate \/ hsame row provenance \/ hsame row name)
          (fun row : BHist => hsame row name /\ Cont betaStep betaStar betaRead /\
            Cont frontier value substRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, betaRoute, substRoute⟩
  }
  exact ⟨cert, betaReadUnary, substReadUnary⟩

end BEDC.Derived.ClosurePreservationAuditWitnessUp
