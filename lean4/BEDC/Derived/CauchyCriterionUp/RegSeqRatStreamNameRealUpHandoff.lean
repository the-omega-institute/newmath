import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_regseqrat_streamname_realup_handoff [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      streamWindow sourceRead handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory streamWindow →
        Cont streamWindow window sourceRead →
          Cont sourceRead regseq handoff →
            Cont handoff realSeal sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory window ∧ UnaryHistory streamWindow ∧ UnaryHistory sourceRead ∧
                  UnaryHistory regseq ∧ UnaryHistory handoff ∧ UnaryHistory realSeal ∧
                    UnaryHistory sealRead ∧ Cont window modulus tolerance ∧
                      Cont tolerance ledger regseq ∧ Cont streamWindow window sourceRead ∧
                        Cont sourceRead regseq handoff ∧ Cont handoff realSeal sealRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier streamWindowUnary streamWindowSource sourceRegseqHandoff
    handoffRealSealSealRead sealPkg
  obtain ⟨windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamWindowUnary windowUnary streamWindowSource
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary realSealUnary handoffRealSealSealRead
  exact
    ⟨windowUnary, streamWindowUnary, sourceUnary, regseqUnary, handoffUnary, realSealUnary,
      sealReadUnary, windowModulusTolerance, toleranceLedgerRegseq, streamWindowSource,
      sourceRegseqHandoff, handoffRealSealSealRead, endpointPkg, sealPkg⟩

end BEDC.Derived.CauchyCriterionUp
