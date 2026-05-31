import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceNamecertLedgerTransport [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      transportedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier metric complete separable stream readback
        ledger transport replay provenance localName bundle pkg ->
      Cont transport ledger transportedLedger ->
        PkgSig bundle transportedLedger pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row transportedLedger ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                  hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                    hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row transportedLedger)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle transportedLedger pkg ∧
                  Cont transport ledger transportedLedger)
              hsame ∧
            UnaryHistory transportedLedger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportLedgerRoute transportedPkg
  obtain ⟨_metricUnary, _completeUnary, _separableUnary, _streamUnary, _readbackUnary,
    ledgerUnary, transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    _carrierPkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedLedger :=
    unary_cont_closed transportUnary ledgerUnary transportLedgerRoute
  have sourceTransported :
      (fun row : BHist => hsame row transportedLedger ∧ UnaryHistory row)
          transportedLedger := by
    exact ⟨hsame_refl transportedLedger, transportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row transportedLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle transportedLedger pkg ∧
              Cont transport ledger transportedLedger)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedLedger sourceTransported
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportedPkg, transportLedgerRoute⟩
  }
  exact ⟨cert, transportedUnary⟩

end BEDC.Derived.PolishspaceUp
