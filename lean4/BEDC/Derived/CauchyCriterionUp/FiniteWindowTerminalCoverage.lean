import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_window_terminal_coverage [AskSetup]
    [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont realSeal transport terminal ->
        PkgSig bundle terminal pkg ->
          UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
              UnaryHistory transport ∧ UnaryHistory terminal ∧ Cont window modulus tolerance ∧
                Cont tolerance ledger regseq ∧ Cont regseq realSeal transport ∧
                  Cont realSeal transport terminal ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier realSealTransportTerminal terminalPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realSealUnary transportUnary realSealTransportTerminal
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      transportUnary, terminalUnary, windowModulusTolerance, toleranceLedgerRegseq,
      regseqRealSealTransport, realSealTransportTerminal, endpointPkg, terminalPkg⟩

end BEDC.Derived.CauchyCriterionUp
