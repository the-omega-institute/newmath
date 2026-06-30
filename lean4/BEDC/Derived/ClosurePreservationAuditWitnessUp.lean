import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosurePreservationAuditWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.ClosurePreservationAuditWitnessUp
