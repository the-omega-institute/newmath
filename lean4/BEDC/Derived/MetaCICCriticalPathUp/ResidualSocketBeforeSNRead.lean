import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualSocketBeforeSNRead [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal schedule residual socket finiteObs subjectRead
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName schedule →
        Cont schedule discharge residual →
          Cont residual handoff socket →
            Cont socket normalForm finiteObs →
              Cont finiteObs discharge subjectRead →
                Cont subjectRead realSeal endpoint →
                  PkgSig bundle endpoint pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row schedule ∨ hsame row residual ∨ hsame row socket ∨
                            hsame row finiteObs ∨ hsame row subjectRead ∨ hsame row endpoint)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalSchedule scheduleDischargeResidual residualHandoffSocket
    socketNormalFinite finiteDischargeSubject subjectRealEndpoint endpointPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalSchedule
  have residualUnary : UnaryHistory residual :=
    unary_cont_closed scheduleUnary dischargeUnary scheduleDischargeResidual
  have socketUnary : UnaryHistory socket :=
    unary_cont_closed residualUnary handoffUnary residualHandoffSocket
  have finiteUnary : UnaryHistory finiteObs :=
    unary_cont_closed socketUnary normalFormUnary socketNormalFinite
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed finiteUnary dischargeUnary finiteDischargeSubject
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed subjectUnary realSealUnary subjectRealEndpoint
  have sourceEndpoint :
      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row) endpoint := by
    exact ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row residual ∨ hsame row socket ∨
              hsame row finiteObs ∨ hsame row subjectRead ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg, realSealPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
