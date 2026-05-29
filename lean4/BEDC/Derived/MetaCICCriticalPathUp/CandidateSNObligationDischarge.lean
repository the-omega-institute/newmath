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

theorem MetaCICCriticalPathCandidateSNObligationDischarge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidate routeRead dischargeRead budgetRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      UnaryHistory candidate →
        Cont candidate strongNorm routeRead →
          Cont routeRead handoff dischargeRead →
            Cont dyadic stream regseq →
              Cont regseq realSeal budgetRead →
                PkgSig bundle dischargeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidate ∨ hsame row strongNorm ∨ hsame row handoff ∨
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal ∨ hsame row dischargeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle dischargeRead pkg ∧
                          PkgSig bundle realSeal pkg ∧
                            Cont routeRead handoff dischargeRead)
                      hsame ∧
                    UnaryHistory routeRead ∧ UnaryHistory dischargeRead ∧
                      PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger candidateUnary candidateStrongNormRoute routeHandoffDischarge
    dyadicStreamRegseq regseqRealSealBudget dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateUnary strongNormUnary candidateStrongNormRoute
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed routeReadUnary handoffUnary routeHandoffDischarge
  have _budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealBudget
  have _regseqRouteWitness : Cont dyadic stream regseq := dyadicStreamRegseq
  have dischargeSource :
      (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row) dischargeRead := by
    exact ⟨hsame_refl dischargeRead, dischargeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row strongNorm ∨ hsame row handoff ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle dischargeRead pkg ∧
              PkgSig bundle realSeal pkg ∧ Cont routeRead handoff dischargeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeRead dischargeSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dischargePkg, realSealPkg, routeHandoffDischarge⟩
  }
  exact ⟨cert, routeReadUnary, dischargeReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
