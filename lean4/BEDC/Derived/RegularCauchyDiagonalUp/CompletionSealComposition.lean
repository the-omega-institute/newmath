import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_completion_seal_composition [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow completionRead alternateRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont selectedWindow regseqRead alternateRead ->
            Cont regseqRead realSeal sealRead ->
              PkgSig bundle completionRead pkg ->
                PkgSig bundle alternateRead pkg ->
                  PkgSig bundle sealRead pkg ->
                    hsame completionRead alternateRead ∧ UnaryHistory selectedWindow ∧
                      UnaryHistory completionRead ∧ UnaryHistory alternateRead ∧
                        UnaryHistory sealRead ∧ hsame windowLedger sealRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                            PkgSig bundle alternateRead pkg ∧
                              PkgSig bundle sealRead pkg := by
  intro carrier windowSelection completionRoute alternateRoute sealRoute
  intro completionPkg alternatePkg sealPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRoute
  have alternateUnary : UnaryHistory alternateRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary alternateRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealRoute
  have completionSameAlternate : hsame completionRead alternateRead :=
    cont_deterministic completionRoute alternateRoute
  have ledgerSameSeal : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealRoute
  exact
    ⟨completionSameAlternate, selectedWindowUnary, completionUnary, alternateUnary, sealUnary,
      ledgerSameSeal, provenancePkg, completionPkg, alternatePkg, sealPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
