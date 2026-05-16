import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_real_seal_unique_finite_route
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont route endpoint terminal ->
        Cont route endpoint terminal' ->
          PkgSig bundle terminal pkg ->
            PkgSig bundle terminal' pkg ->
              hsame terminal terminal' ∧ UnaryHistory terminal ∧ UnaryHistory terminal' ∧
                Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                  Cont regseq realSeal transport ∧ Cont transport localCert route ∧
                    Cont route provenance endpoint ∧ Cont route endpoint terminal ∧
                      Cont route endpoint terminal' ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle terminal pkg ∧ PkgSig bundle terminal' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute terminalRoute' terminalPkg terminalPkg'
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealTransport,
    transportLocalCertRoute, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed routeUnary endpointUnary terminalRoute
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed routeUnary endpointUnary terminalRoute'
  have sameTerminal : hsame terminal terminal' :=
    cont_deterministic terminalRoute terminalRoute'
  exact
    ⟨sameTerminal, terminalUnary, terminalUnary', windowModulusTolerance,
      toleranceLedgerRegseq, regseqRealSealTransport, transportLocalCertRoute,
      routeProvenanceEndpoint, terminalRoute, terminalRoute', endpointPkg, terminalPkg,
      terminalPkg'⟩

end BEDC.Derived.CauchyCriterionUp
