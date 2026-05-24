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

theorem FiniteLebesgueNumberUniformConsumerDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead uniformRead
      uniformRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead nameRow uniformRead ->
          Cont compactRead nameRow uniformRead' ->
            PkgSig bundle uniformRead pkg ->
              PkgSig bundle uniformRead' pkg ->
                UnaryHistory radius ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                  UnaryHistory uniformRead' ∧ hsame uniformRead uniformRead' ∧
                    Cont radius mesh compactRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle uniformRead pkg ∧ PkgSig bundle uniformRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier radiusMeshCompact compactNameUniform compactNameUniform' uniformPkg
    uniformPkg'
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  have uniformUnary' : UnaryHistory uniformRead' :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform'
  have sameUniform : hsame uniformRead uniformRead' :=
    cont_deterministic compactNameUniform compactNameUniform'
  exact
    ⟨radiusUnary, compactUnary, uniformUnary, uniformUnary', sameUniform,
      radiusMeshCompact, provenancePkg, uniformPkg, uniformPkg'⟩

theorem FiniteLebesgueNumberCompactConsumerDeterminacyPackage [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactMetricRead
      compactNetRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactMetricRead ->
        Cont radius mesh compactNetRead ->
          Cont compactNetRead nameRow uniformRead ->
            PkgSig bundle compactMetricRead pkg ->
              PkgSig bundle uniformRead pkg ->
                UnaryHistory radius ∧ UnaryHistory compactMetricRead ∧
                  UnaryHistory compactNetRead ∧ UnaryHistory uniformRead ∧
                    hsame compactMetricRead compactNetRead ∧
                      Cont radius mesh compactMetricRead ∧ Cont radius mesh compactNetRead ∧
                        Cont compactNetRead nameRow uniformRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle compactMetricRead pkg ∧
                              PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier radiusMeshCompactMetric radiusMeshCompactNet compactNetNameUniform
    compactMetricPkg uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompactMetric
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompactNet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactNetUnary nameRowUnary compactNetNameUniform
  have sameCompact : hsame compactMetricRead compactNetRead :=
    cont_deterministic radiusMeshCompactMetric radiusMeshCompactNet
  exact
    ⟨radiusUnary, compactMetricUnary, compactNetUnary, uniformUnary, sameCompact,
      radiusMeshCompactMetric, radiusMeshCompactNet, compactNetNameUniform, provenancePkg,
      compactMetricPkg, uniformPkg⟩

def FiniteLebesgueNumberRadiusConsumerDeterminacyLedger [AskSetup] [PackageSetup]
    (cover radius mesh source regular real transport route provenance nameRow compactConsumer
      uniformConsumer : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory source ∧
    UnaryHistory regular ∧ UnaryHistory real ∧ UnaryHistory compactConsumer ∧
      UnaryHistory uniformConsumer ∧ Cont cover radius source ∧ Cont source mesh regular ∧
        Cont regular route real ∧ Cont real nameRow compactConsumer ∧
          Cont compactConsumer transport uniformConsumer ∧ PkgSig bundle provenance pkg

theorem FiniteLebesgueNumberRadiusConsumerDeterminacyLedger_fields [AskSetup]
    [PackageSetup]
    {cover radius mesh source regular real transport route provenance nameRow compactConsumer
      uniformConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRadiusConsumerDeterminacyLedger cover radius mesh source regular real
        transport route provenance nameRow compactConsumer uniformConsumer bundle pkg ->
      Cont cover radius source ∧ Cont source mesh regular ∧ Cont regular route real ∧
        Cont real nameRow compactConsumer ∧ Cont compactConsumer transport uniformConsumer ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro ledger
  exact
    ⟨ledger.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.FiniteLebesgueNumberUp
