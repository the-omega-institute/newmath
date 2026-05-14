import BEDC.Derived.CauchyLimitSealUp
import BEDC.Derived.RealTailAgreementSealUp.TerminalRoute

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealTailAgreementSealUp

theorem CauchyLimitSealCarrier_real_tail_agreement_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint R S W D A P
      leftRead rightRead leftDyadic rightDyadic agreement terminal comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
        rightDyadic agreement terminal ->
        Cont endpoint terminal comparison ->
          UnaryHistory terminal ∧ UnaryHistory comparison ∧ hsame agreement (append leftDyadic A) ∧
            hsame terminal (append agreement P) ∧ Cont agreement P terminal ∧
              Cont endpoint terminal comparison ∧ hsame endpoint (append provenance localCert) ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier route endpointTerminalComparison
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, endpointSame, endpointPkg⟩ := carrier
  have routeExhaustion :=
    RealTailAgreementSealTerminalRoute_exhaustion route
  have routeUnique :=
    RealTailAgreementSeal_budget_route_uniqueness route
  have terminalUnary : UnaryHistory terminal :=
    routeExhaustion.right.right.right.left
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed endpointUnary terminalUnary endpointTerminalComparison
  exact
    ⟨terminalUnary, comparisonUnary, routeUnique.left, routeUnique.right.left,
      routeUnique.right.right.right.right.right, endpointTerminalComparison, endpointSame,
      endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
