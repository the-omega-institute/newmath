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

theorem MetaCICCriticalPathExactBoundaryPrefixDeterminacy [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal budgetPrefix schedulePrefix readbackPrefix
      sealPrefix exactBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont dyadic stream budgetPrefix ->
        Cont budgetPrefix regseq schedulePrefix ->
          Cont schedulePrefix realSeal readbackPrefix ->
            Cont readbackPrefix handoff sealPrefix ->
              hsame exactBoundary sealPrefix ->
                PkgSig bundle sealPrefix pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row budgetPrefix ∨
                            hsame row schedulePrefix ∨ hsame row readbackPrefix ∨
                              hsame row sealPrefix ∨ hsame row exactBoundary)
                      (fun row : BHist =>
                        PkgSig bundle sealPrefix pkg ∧ hsame row exactBoundary)
                      hsame ∧
                    UnaryHistory budgetPrefix ∧ UnaryHistory schedulePrefix ∧
                      UnaryHistory readbackPrefix ∧ UnaryHistory sealPrefix ∧
                        UnaryHistory exactBoundary := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamBudget budgetRegseqSchedule scheduleRealSealReadback
    readbackHandoffSeal exactBoundarySeal sealPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamBudget
  have schedulePrefixUnary : UnaryHistory schedulePrefix :=
    unary_cont_closed budgetPrefixUnary regseqUnary budgetRegseqSchedule
  have readbackPrefixUnary : UnaryHistory readbackPrefix :=
    unary_cont_closed schedulePrefixUnary realSealUnary scheduleRealSealReadback
  have sealPrefixUnary : UnaryHistory sealPrefix :=
    unary_cont_closed readbackPrefixUnary handoffUnary readbackHandoffSeal
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_transport sealPrefixUnary (hsame_symm exactBoundarySeal)
  have sourceExact :
      (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row) exactBoundary := by
    exact ⟨hsame_refl exactBoundary, exactBoundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row budgetPrefix ∨ hsame row schedulePrefix ∨
                hsame row readbackPrefix ∨ hsame row sealPrefix ∨ hsame row exactBoundary)
          (fun row : BHist =>
            PkgSig bundle sealPrefix pkg ∧ hsame row exactBoundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exactBoundary sourceExact
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨sealPkg, source.left⟩
  }
  exact
    ⟨cert, budgetPrefixUnary, schedulePrefixUnary, readbackPrefixUnary, sealPrefixUnary,
      exactBoundaryUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
