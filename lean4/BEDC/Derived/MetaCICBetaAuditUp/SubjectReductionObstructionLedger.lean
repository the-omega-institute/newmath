import BEDC.Derived.MetaCICBetaAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICBetaAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

theorem MetaCICBetaAudit_subject_reduction_obstruction_ledger [AskSetup] [PackageSetup]
    {S V T F O H C P N subjectRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont O C subjectRead →
      PkgSig bundle P pkg →
        UnaryHistory O →
          UnaryHistory C →
            UnaryHistory subjectRead ∧ Cont O C subjectRead ∧ PkgSig bundle P pkg ∧
              List.Mem (metaCICBetaAuditEncodeBHist O)
                (metaCICBetaAuditToEventFlow (MetaCICBetaAuditUp.mk S V T F O H C P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro obstructionRoute provenancePkg obstructionUnary continuationUnary
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed obstructionUnary continuationUnary obstructionRoute
  have obstructionMember :
      List.Mem (metaCICBetaAuditEncodeBHist O)
        [metaCICBetaAuditEncodeBHist S, metaCICBetaAuditEncodeBHist V,
          metaCICBetaAuditEncodeBHist T, metaCICBetaAuditEncodeBHist F,
          metaCICBetaAuditEncodeBHist O, metaCICBetaAuditEncodeBHist H,
          metaCICBetaAuditEncodeBHist C, metaCICBetaAuditEncodeBHist P,
          metaCICBetaAuditEncodeBHist N] :=
    List.Mem.tail _
      (List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _))))
  exact
    ⟨subjectUnary, obstructionRoute, provenancePkg, obstructionMember⟩

end BEDC.Derived.MetaCICBetaAuditUp
