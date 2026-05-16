import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_certificate_compiler_route_nonescape
    [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      compilerRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      Cont source target compilerRead →
        Cont compilerRead cert finalRead →
          PkgSig bundle finalRead pkg →
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory edgeAdmission ∧ UnaryHistory classifierLift ∧
                UnaryHistory compilerRead ∧ UnaryHistory finalRead ∧
                  Cont source graph edgeAdmission ∧
                    Cont edgeAdmission classifierLift target ∧
                      Cont source target compilerRead ∧ Cont compilerRead cert finalRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg ∧
                          PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier compilerRoute finalRoute finalPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
    _transportUnary, _routesUnary, _provenanceUnary, certUnary, sourceGraphAdmission,
    admissionClassifierTarget, _transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed sourceUnary targetUnary compilerRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed compilerUnary certUnary finalRoute
  exact
    ⟨sourceUnary, targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
      compilerUnary, finalUnary, sourceGraphAdmission, admissionClassifierTarget,
      compilerRoute, finalRoute, provenancePkg, certPkg, finalPkg⟩

end BEDC.Derived.KernelMorphismUp
