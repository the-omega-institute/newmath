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

theorem MetaCICCriticalPathResidualBudgetSocketRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualBudget substitutionBoundary
      premiseLedger localDiamond socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream residualBudget →
        Cont residualBudget obstruction substitutionBoundary →
          Cont substitutionBoundary discharge premiseLedger →
            Cont premiseLedger normalForm localDiamond →
              Cont localDiamond discharge socketRead →
                PkgSig bundle socketRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row residualBudget ∨ hsame row substitutionBoundary ∨
                          hsame row premiseLedger ∨ hsame row localDiamond ∨
                            hsame row socketRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                          Cont localDiamond discharge socketRead)
                      hsame ∧
                    UnaryHistory residualBudget ∧ UnaryHistory substitutionBoundary ∧
                      UnaryHistory premiseLedger ∧ UnaryHistory localDiamond ∧
                        UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamResidual residualObstructionSubstitution
    substitutionDischargePremise premiseNormalFormDiamond localDiamondDischargeSocket
    socketReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have residualBudgetUnary : UnaryHistory residualBudget :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamResidual
  have substitutionBoundaryUnary : UnaryHistory substitutionBoundary :=
    unary_cont_closed residualBudgetUnary obstructionUnary residualObstructionSubstitution
  have premiseLedgerUnary : UnaryHistory premiseLedger :=
    unary_cont_closed substitutionBoundaryUnary dischargeUnary substitutionDischargePremise
  have localDiamondUnary : UnaryHistory localDiamond :=
    unary_cont_closed premiseLedgerUnary normalFormUnary premiseNormalFormDiamond
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed localDiamondUnary dischargeUnary localDiamondDischargeSocket
  have sourceSocketRead :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualBudget ∨ hsame row substitutionBoundary ∨
              hsame row premiseLedger ∨ hsame row localDiamond ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont localDiamond discharge socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocketRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketReadPkg, localDiamondDischargeSocket⟩
  }
  exact
    ⟨cert, residualBudgetUnary, substitutionBoundaryUnary, premiseLedgerUnary,
      localDiamondUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
