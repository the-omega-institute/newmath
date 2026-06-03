import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalizationBudgetNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal l10Read normalBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal l10Read →
          Cont continuation l10Read normalBudget →
            PkgSig bundle normalBudget pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row normalBudget ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row unblock ∨
                      hsame row handoff ∨ hsame row continuation ∨ hsame row dyadic ∨
                        hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                          hsame row l10Read ∨ hsame row normalBudget)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle normalBudget pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory l10Read ∧ UnaryHistory normalBudget ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealL10 continuationL10Budget normalBudgetPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealL10
  have normalBudgetUnary : UnaryHistory normalBudget :=
    unary_cont_closed continuationUnary l10Unary continuationL10Budget
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row unblock ∨
              hsame row handoff ∨ hsame row continuation ∨ hsame row dyadic ∨
                hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                  hsame row l10Read ∨ hsame row normalBudget)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle normalBudget pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro normalBudget ⟨hsame_refl normalBudget, normalBudgetUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, normalBudgetPkg, realSealPkg⟩
  }
  exact ⟨cert, l10Unary, normalBudgetUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
