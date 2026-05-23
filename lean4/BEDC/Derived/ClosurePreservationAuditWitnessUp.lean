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

end BEDC.Derived.ClosurePreservationAuditWitnessUp
