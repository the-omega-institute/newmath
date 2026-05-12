import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_namecert_consumer_surface [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      consumerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal consumerSeal ->
          PkgSig bundle selectedWindow pkg ->
            PkgSig bundle consumerSeal pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row consumerSeal ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist => hsame row consumerSeal ∧ Cont regseqRead realSeal row)
                (fun _row : BHist =>
                  RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
                    windowLedger provenance localCert bundle pkg ∧ PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory selectedWindow ∧ hsame windowLedger consumerSeal := by
  intro carrier windowSelection consumerSealRow _selectedPkg consumerSealPkg
  have carrierData := carrier
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have consumerSealUnary : UnaryHistory consumerSeal :=
    unary_cont_closed regseqReadUnary realSealUnary consumerSealRow
  have ledgerSameConsumer : hsame windowLedger consumerSeal :=
    cont_deterministic regseqSealLedger consumerSealRow
  have sourceConsumer :
      hsame consumerSeal consumerSeal ∧ UnaryHistory consumerSeal ∧
        PkgSig bundle consumerSeal pkg :=
    ⟨hsame_refl consumerSeal, consumerSealUnary, consumerSealPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerSeal ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row consumerSeal ∧ Cont regseqRead realSeal row)
        (fun _row : BHist =>
          RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
            provenance localCert bundle pkg ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerSeal sourceConsumer
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨hsame_refl consumerSeal, consumerSealRow⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨carrierData, provenancePkg⟩
  }
  exact ⟨cert, selectedWindowUnary, ledgerSameConsumer⟩

end BEDC.Derived.RegularCauchyDiagonalUp
