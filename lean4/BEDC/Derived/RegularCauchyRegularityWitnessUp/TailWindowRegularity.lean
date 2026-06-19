import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

theorem RegularCauchyRegularityWitnessTailWindowRegularity [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N tailRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont Omega R tailRead →
        Cont tailRead Q sealRead →
          Cont sealRead E completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory Omega ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                  Cont j Omega R ∧ Cont R Q E ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier omegaTail tailSeal sealCompletion completionPkg
  obtain ⟨_unaryS, _unaryMu, _unaryJ, unaryOmega, unaryR, unaryQ, unaryE,
    _unaryH, _unaryC, _unaryP, _unaryN, _routeSMuJ, routeJOmegaR, routeRQE,
    _routeEHC, _pkgP, _pkgN⟩ := carrier
  have unaryTailRead : UnaryHistory tailRead :=
    unary_cont_closed unaryOmega unaryR omegaTail
  have unarySealRead : UnaryHistory sealRead :=
    unary_cont_closed unaryTailRead unaryQ tailSeal
  have unaryCompletionRead : UnaryHistory completionRead :=
    unary_cont_closed unarySealRead unaryE sealCompletion
  exact
    ⟨unaryOmega, unaryR, unaryQ, unaryE, unaryTailRead, unarySealRead,
      unaryCompletionRead, routeJOmegaR, routeRQE, completionPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
