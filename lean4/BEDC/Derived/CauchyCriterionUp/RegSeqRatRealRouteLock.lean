import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_regseqrat_real_route_lock [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      streamWindow handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory streamWindow →
        Cont streamWindow regseq handoff →
          Cont handoff realSeal sealRead →
            PkgSig bundle handoff pkg →
              PkgSig bundle sealRead pkg →
                UnaryHistory streamWindow ∧ UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                  Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                    Cont streamWindow regseq handoff ∧ Cont handoff realSeal sealRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle handoff pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier streamWindowUnary streamRegseqHandoff handoffRealSealRead handoffPkg
    sealReadPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed streamWindowUnary regseqUnary streamRegseqHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary realSealUnary handoffRealSealRead
  exact
    ⟨streamWindowUnary, handoffUnary, sealReadUnary, windowModulusTolerance,
      toleranceLedgerRegseq, streamRegseqHandoff, handoffRealSealRead, endpointPkg,
      handoffPkg, sealReadPkg⟩

end BEDC.Derived.CauchyCriterionUp
