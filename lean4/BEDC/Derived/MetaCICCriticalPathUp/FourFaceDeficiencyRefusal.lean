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

theorem MetaCICCriticalPathFourFaceDeficiencyRefusal [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal statusRead deficientFace :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              Cont realSeal localName statusRead →
                PkgSig bundle statusRead pkg →
                  Cont statusRead deficientFace dischargeSocket →
                    SemanticNameCert
                        (fun row : BHist => hsame row dischargeSocket ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                            hsame row regReadback ∨ hsame row realSeal ∨
                              hsame row deficientFace ∨ hsame row dischargeSocket)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont statusRead deficientFace dischargeSocket ∧
                            PkgSig bundle statusRead pkg)
                        hsame ∧
                      UnaryHistory dischargeSocket := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal sealLocalNameStatus statusReadPkg statusDeficientSocket
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed realSealUnary localNameUnary sealLocalNameStatus
  have deficientFaceUnary : UnaryHistory deficientFace :=
    (unary_cont_factors_from_result statusDeficientSocket dischargeSocketUnary).right
  have sourceSocket :
      (fun row : BHist => hsame row dischargeSocket ∧ UnaryHistory row) dischargeSocket := by
    exact ⟨hsame_refl dischargeSocket, dischargeSocketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeSocket ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regReadback ∨
              hsame row realSeal ∨ hsame row deficientFace ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont statusRead deficientFace dischargeSocket ∧
              PkgSig bundle statusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeSocket sourceSocket
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
      exact ⟨source.right, statusDeficientSocket, statusReadPkg⟩
  }
  exact ⟨cert, dischargeSocketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
