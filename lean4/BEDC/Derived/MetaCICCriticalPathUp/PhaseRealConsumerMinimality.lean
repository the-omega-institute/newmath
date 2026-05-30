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

theorem MetaCICCriticalPathPhaseRealConsumerMinimality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              Cont realSeal localName consumerRead →
                PkgSig bundle consumerRead pkg →
                  PkgSig bundle provenance pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                            hsame row regReadback ∨ hsame row realSeal ∨
                              hsame row consumerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧
                            Cont realSeal localName consumerRead)
                        hsame ∧
                      UnaryHistory dyadicBudget ∧ UnaryHistory streamSchedule ∧
                        UnaryHistory regReadback ∧ UnaryHistory realSeal ∧
                          UnaryHistory consumerRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal sealLocalNameConsumer consumerReadPkg provenancePkgInput
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
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
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed realSealUnary localNameUnary sealLocalNameConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle consumerRead pkg ∧
              Cont realSeal localName consumerRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact ⟨source.right, consumerReadPkg, sealLocalNameConsumer⟩
  }
  exact
    ⟨cert, dyadicBudgetUnary, streamScheduleUnary, regReadbackUnary, realSealUnary,
      consumerReadUnary, provenancePkgInput⟩

end BEDC.Derived.MetaCICCriticalPathUp
