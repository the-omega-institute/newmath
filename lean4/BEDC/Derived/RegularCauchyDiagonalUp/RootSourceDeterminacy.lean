import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RegularCauchyDiagonalCarrier_root_source_determinacy [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead regseqRead' realSeal windowLedger windowLedger'
      provenance provenance' localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead' realSeal windowLedger'
          provenance' localCert bundle pkg ->
        hsame regseqRead regseqRead' ∧ hsame windowLedger windowLedger' ∧
          hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro leftCarrier rightCarrier
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, _realSealUnary,
    _windowLedgerUnary, _provenanceUnary, _localCertUnary, leftRatStream,
    leftRegseqSeal, leftSealLocal, _leftPkg⟩ := leftCarrier
  obtain ⟨_ratSeedUnary', _streamWindowUnary', _regseqReadUnary', _realSealUnary',
    _windowLedgerUnary', _provenanceUnary', _localCertUnary', rightRatStream,
    rightRegseqSeal, rightSealLocal, _rightPkg⟩ := rightCarrier
  have regseqSame : hsame regseqRead regseqRead' :=
    cont_deterministic leftRatStream rightRatStream
  have windowLedgerSame : hsame windowLedger windowLedger' :=
    cont_respects_hsame regseqSame (hsame_refl realSeal) leftRegseqSeal rightRegseqSeal
  have provenanceSame : hsame provenance provenance' :=
    cont_deterministic leftSealLocal rightSealLocal
  exact ⟨regseqSame, windowLedgerSame, provenanceSame⟩

end BEDC.Derived.RegularCauchyDiagonalUp
