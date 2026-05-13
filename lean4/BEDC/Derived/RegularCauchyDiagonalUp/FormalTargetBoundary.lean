import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_formal_target_boundary [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow fiberRead sealRead completionRead directCompletion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead fiberRead ->
          Cont regseqRead realSeal sealRead ->
            Cont selectedWindow regseqRead completionRead ->
              Cont windowLedger (append streamWindow regseqRead) directCompletion ->
                PkgSig bundle fiberRead pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      PkgSig bundle directCompletion pkg ->
                        hsame fiberRead completionRead ∧ hsame completionRead directCompletion ∧
                          hsame windowLedger sealRead ∧ UnaryHistory directCompletion ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier windowSelection fiberRoute sealRoute completionRoute directCompletionRoute
    _fiberPkg _sealPkg _completionPkg _directCompletionPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have fiberSameCompletion : hsame fiberRead completionRead :=
    cont_deterministic fiberRoute completionRoute
  have completionDirectRoute :
      Cont windowLedger (append streamWindow regseqRead) completionRead := by
    cases windowSelection
    exact completionRoute.trans (append_assoc windowLedger streamWindow regseqRead)
  have completionSameDirect : hsame completionRead directCompletion :=
    cont_deterministic completionDirectRoute directCompletionRoute
  have ledgerSameSeal : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealRoute
  have streamRegseqUnary : UnaryHistory (append streamWindow regseqRead) :=
    unary_cont_closed streamWindowUnary regseqReadUnary (cont_intro rfl)
  have directCompletionUnary : UnaryHistory directCompletion :=
    unary_cont_closed windowLedgerUnary streamRegseqUnary directCompletionRoute
  exact
    ⟨fiberSameCompletion, completionSameDirect, ledgerSameSeal, directCompletionUnary,
      provenancePkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
