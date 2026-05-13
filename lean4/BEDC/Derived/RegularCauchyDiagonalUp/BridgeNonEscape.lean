import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RegularCauchyDiagonalCarrier_bridge_non_escape [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal sealRead ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row selectedWindow ∧ Cont windowLedger streamWindow row ∧
                  RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
                    windowLedger provenance localCert bundle pkg)
              (fun row : BHist => hsame row selectedWindow)
              (fun row : BHist => hsame row selectedWindow ∧ PkgSig bundle provenance pkg)
              hsame ∧
            hsame windowLedger sealRead := by
  intro carrier windowSelection sealReadRow
  have carrierProof := carrier
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, _realSealUnary,
    _windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    ledgerSealRow, _sealLocalProvenance, pkgSig⟩ := carrier
  have sourceWindow :
      (fun row : BHist =>
        hsame row selectedWindow ∧ Cont windowLedger streamWindow row ∧
          RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
            provenance localCert bundle pkg) selectedWindow := by
    exact ⟨hsame_refl selectedWindow, windowSelection, carrierProof⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row selectedWindow ∧ Cont windowLedger streamWindow row ∧
            RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
              windowLedger provenance localCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro selectedWindow sourceWindow
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        have otherSelected : hsame other selectedWindow :=
          hsame_trans (hsame_symm same) source.left
        have otherCont : Cont windowLedger streamWindow other :=
          cont_result_hsame_transport source.right.left same
        exact ⟨otherSelected, otherCont, source.right.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row selectedWindow ∧ Cont windowLedger streamWindow row ∧
              RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
                windowLedger provenance localCert bundle pkg)
          (fun row : BHist => hsame row selectedWindow)
          (fun row : BHist => hsame row selectedWindow ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := core
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, pkgSig⟩
  }
  have sealSame : hsame windowLedger sealRead :=
    cont_deterministic ledgerSealRow sealReadRow
  exact ⟨cert, sealSame⟩

end BEDC.Derived.RegularCauchyDiagonalUp
