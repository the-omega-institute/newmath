import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusRowDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead uniformRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead nameRow uniformRead ->
          PkgSig bundle uniformRead pkg ->
            UnaryHistory radius ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
              Cont radius mesh compactRead ∧ Cont compactRead nameRow uniformRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  exact
    ⟨radiusUnary, compactUnary, uniformUnary, radiusMeshCompact, compactNameUniform,
      provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberRealPhaseSourceExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead terminalRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
      Cont auditRead terminalRead consumerRead ->
      UnaryHistory terminalRead ->
      PkgSig bundle consumerRead pkg ->
        UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
          UnaryHistory mesh ∧ UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
            UnaryHistory consumerRead ∧ Cont cover window radius ∧ Cont radius mesh route ∧
              Cont route nameRow auditRead ∧ Cont auditRead terminalRead consumerRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditTerminalConsumer terminalUnary consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary terminalUnary auditTerminalConsumer
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, terminalUnary,
      consumerUnary, coverWindowRadius, radiusMeshRoute, routeNameAudit,
      auditTerminalConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
