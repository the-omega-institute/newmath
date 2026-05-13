import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitTransportCarrier [AskSetup] [PackageSetup]
    (source window dyadic sealRow transport routes provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory sealRow ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ Cont source window dyadic ∧
      Cont dyadic sealRow routes ∧ Cont provenance sealRow cert ∧
        hsame transport (append source sealRow) ∧ PkgSig bundle cert pkg

theorem RegularCauchyLimitTransportCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance cert
        bundle pkg ->
      UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory sealRow ∧
        UnaryHistory routes ∧ Cont source window dyadic ∧ Cont dyadic sealRow routes ∧
          hsame transport (append source sealRow) ∧ PkgSig bundle cert pkg := by
  intro carrier
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, _transportUnary,
    _provenanceUnary, sourceWindowDyadic, dyadicSealRoutes, _provenanceSealCert,
    transportMatchesSeal, certPkg⟩ := carrier
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed dyadicUnary sealUnary dyadicSealRoutes
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, routesUnary, sourceWindowDyadic,
      dyadicSealRoutes, transportMatchesSeal, certPkg⟩

end BEDC.Derived.RegularCauchyLimitTransportUp
