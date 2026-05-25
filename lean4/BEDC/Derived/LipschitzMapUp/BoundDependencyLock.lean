import BEDC.Derived.LipschitzMapUp

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LipschitzMapCarrier_bound_dependency_lock [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg →
      Cont bound modulus consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧ UnaryHistory graph ∧
            UnaryHistory modulus ∧ UnaryHistory consumer ∧ Cont graph bound modulus ∧
              Cont bound modulus consumer ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier boundModulusConsumer consumerPkg
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, _transportsUnary, _routesUnary,
    _localCertUnary, graphBoundModulus, _modulusRoutesProvenance, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed boundUnary modulusUnary boundModulusConsumer
  exact
    ⟨sourceUnary, targetUnary, boundUnary, graphUnary, modulusUnary, consumerUnary,
      graphBoundModulus, boundModulusConsumer, provenancePkg, consumerPkg⟩

theorem LipschitzMapCarrier_transported_bound_dependency_lock [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert source' target'
      bound' graph' modulus' consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg →
      hsame source source' →
        hsame target target' →
          hsame bound bound' →
            hsame graph graph' →
              Cont graph' bound' modulus' →
                Cont bound' modulus' consumer →
                  PkgSig bundle consumer pkg →
                    UnaryHistory source' ∧ UnaryHistory target' ∧ UnaryHistory bound' ∧
                      UnaryHistory graph' ∧ UnaryHistory modulus' ∧ UnaryHistory consumer ∧
                        Cont graph' bound' modulus' ∧ Cont bound' modulus' consumer ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSource sameTarget sameBound sameGraph modulusCont'
    boundModulusConsumer consumerPkg
  have transported :=
    LipschitzMapCarrier_bound_transport carrier sameSource sameTarget sameBound sameGraph
      modulusCont'
  exact
    LipschitzMapCarrier_bound_dependency_lock transported.left boundModulusConsumer consumerPkg

theorem LipschitzMapCarrier_identity_bound_dependency_lock [AskSetup] [PackageSetup]
    {source bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory bound →
        UnaryHistory graph →
          UnaryHistory transports →
            UnaryHistory routes →
              UnaryHistory localCert →
                Cont graph bound modulus →
                  Cont modulus routes provenance →
                    PkgSig bundle provenance pkg →
                      Cont bound modulus consumer →
                        PkgSig bundle consumer pkg →
                          UnaryHistory source ∧ UnaryHistory source ∧ UnaryHistory bound ∧
                            UnaryHistory graph ∧ UnaryHistory modulus ∧ UnaryHistory consumer ∧
                              Cont graph bound modulus ∧ Cont bound modulus consumer ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro sourceUnary boundUnary graphUnary transportsUnary routesUnary localCertUnary
    graphBoundModulus modulusRoutesProvenance provenancePkg boundModulusConsumer consumerPkg
  have identityCarrier :=
    LipschitzMapCarrier_identity_carrier_boundary sourceUnary boundUnary graphUnary
      transportsUnary routesUnary localCertUnary graphBoundModulus modulusRoutesProvenance
      provenancePkg
  exact
    LipschitzMapCarrier_bound_dependency_lock identityCarrier.left boundModulusConsumer
      consumerPkg

end BEDC.Derived.LipschitzMapUp
