import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyDiagonalCarrier [AskSetup] [PackageSetup]
    (ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
    UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧ UnaryHistory provenance ∧
      UnaryHistory localCert ∧ Cont ratSeed streamWindow regseqRead ∧
        Cont regseqRead realSeal windowLedger ∧ Cont realSeal localCert provenance ∧
          PkgSig bundle provenance pkg

theorem RegularCauchyDiagonalCarrier_window_coverage [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        PkgSig bundle selectedWindow pkg ->
          UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
            UnaryHistory selectedWindow ∧ Cont windowLedger streamWindow selectedWindow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle selectedWindow pkg := by
  intro carrier windowSelection selectedPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, _realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, selectedWindowUnary,
      windowSelection, provenancePkg, selectedPkg⟩

theorem RegularCauchyDiagonalCarrier_window_ledger_exactness [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow realSeal sealRead ->
          hsame sealRead
              (append ratSeed (append streamWindow (append realSeal (append streamWindow realSeal)))) ∧
            UnaryHistory selectedWindow ∧ UnaryHistory sealRead := by
  intro carrier windowSelection sealRoute
  obtain ⟨ratSeedUnary, streamWindowUnary, _regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, _provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectedWindowUnary realSealUnary sealRoute
  constructor
  · cases ratStreamRegseq
    cases regseqSealLedger
    cases windowSelection
    cases sealRoute
    exact
      (append_assoc (append (append ratSeed streamWindow) realSeal) streamWindow
        realSeal).trans
        ((append_assoc (append ratSeed streamWindow) realSeal
          (append streamWindow realSeal)).trans
          (append_assoc ratSeed streamWindow (append realSeal (append streamWindow realSeal))))
  · exact ⟨selectedWindowUnary, sealReadUnary⟩

end BEDC.Derived.RegularCauchyDiagonalUp
