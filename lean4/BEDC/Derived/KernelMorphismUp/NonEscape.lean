import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_non_escape [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert routeRead
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      Cont provenance cert routeRead →
        Cont routeRead target finalRead →
          PkgSig bundle finalRead pkg →
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory edgeAdmission ∧ UnaryHistory classifierLift ∧
                UnaryHistory routeRead ∧ UnaryHistory finalRead ∧
                  Cont source graph edgeAdmission ∧
                    Cont edgeAdmission classifierLift target ∧
                      Cont provenance cert routeRead ∧ Cont routeRead target finalRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg ∧
                          PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier provenanceCertRoute routeTargetFinal finalPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
    _transportUnary, _routesUnary, provenanceUnary, certUnary, sourceGraphAdmission,
    admissionClassifierTarget, _transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed provenanceUnary certUnary provenanceCertRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed routeReadUnary targetUnary routeTargetFinal
  exact
    ⟨sourceUnary, targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
      routeReadUnary, finalReadUnary, sourceGraphAdmission, admissionClassifierTarget,
      provenanceCertRoute, routeTargetFinal, provenancePkg, certPkg, finalPkg⟩

end BEDC.Derived.KernelMorphismUp
