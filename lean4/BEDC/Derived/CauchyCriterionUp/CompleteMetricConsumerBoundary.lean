import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.CompleteMetricUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_complete_metric_consumer_boundary
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      metricLimit consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.CompleteMetricUp.CompleteMetricLimitWitness (fun h : BHist => UnaryHistory h)
        (fun _ : BHist => regseq) (fun _ : BHist => tolerance) metricLimit ->
      Cont realSeal metricLimit consumer ->
      PkgSig bundle consumer pkg ->
      UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
        UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
          UnaryHistory metricLimit ∧ UnaryHistory consumer ∧ Cont window modulus tolerance ∧
            Cont tolerance ledger regseq ∧ Cont realSeal metricLimit consumer ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier limitWitness realSealMetricLimitConsumer consumerPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have metricLimitUnary : UnaryHistory metricLimit :=
    limitWitness.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary metricLimitUnary realSealMetricLimitConsumer
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      metricLimitUnary, consumerUnary, windowModulusTolerance, toleranceLedgerRegseq,
      realSealMetricLimitConsumer, endpointPkg, consumerPkg⟩

end BEDC.Derived.CauchyCriterionUp
