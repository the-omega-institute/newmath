import BEDC.Derived.MetaCICBetaAuditUp
import BEDC.Derived.MetaCICBetaAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICBetaAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem MetaCICBetaAudit_boundary_obstruction_eventflow_consumer [AskSetup] [PackageSetup]
    {S V T F O H C P N reductionRead conversionRead obstructionRead subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICBetaAuditCarrier S V T F O H C P N
        reductionRead conversionRead obstructionRead →
      Cont O C subjectRead →
        PkgSig bundle P pkg →
          SemanticNameCert
              (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨
                  hsame row O ∨ hsame row reductionRead ∨ hsame row conversionRead ∨
                    hsame row obstructionRead)
              (fun row : BHist =>
                hsame row obstructionRead ∧ Cont S T reductionRead ∧
                  Cont V T conversionRead ∧ Cont conversionRead O obstructionRead)
              hsame ∧
            Cont S T reductionRead ∧ Cont V T conversionRead ∧
              Cont conversionRead O obstructionRead ∧ UnaryHistory subjectRead ∧
                Cont O C subjectRead ∧ PkgSig bundle P pkg ∧
                  List.Mem (metaCICBetaAuditEncodeBHist O)
                    (metaCICBetaAuditToEventFlow (MetaCICBetaAuditUp.mk S V T F O H C P N)) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert EventFlow
  intro carrier subjectRoute provenancePkg
  have boundary :=
    MetaCICBetaAudit_reduction_conversion_boundary
      (S := S) (V := V) (T := T) (F := F) (O := O) (H := H) (C := C)
      (P := P) (N := N) (reductionRead := reductionRead)
      (conversionRead := conversionRead) (obstructionRead := obstructionRead)
      carrier
  obtain ⟨_sUnary, _vUnary, _tUnary, _fUnary, oUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _reductionRoute, _conversionRoute, _obstructionRoute⟩ := carrier
  have subjectLedger :=
    MetaCICBetaAudit_subject_reduction_obstruction_ledger
      (S := S) (V := V) (T := T) (F := F) (O := O) (H := H) (C := C)
      (P := P) (N := N) (subjectRead := subjectRead) (bundle := bundle)
      (pkg := pkg) subjectRoute provenancePkg oUnary cUnary
  obtain ⟨cert, reductionRoute, conversionRoute, obstructionRoute⟩ := boundary
  obtain ⟨subjectUnary, subjectRoute', provenancePkg', obstructionMember⟩ := subjectLedger
  exact
    ⟨cert, reductionRoute, conversionRoute, obstructionRoute, subjectUnary,
      subjectRoute', provenancePkg', obstructionMember⟩

end BEDC.Derived.MetaCICBetaAuditUp
