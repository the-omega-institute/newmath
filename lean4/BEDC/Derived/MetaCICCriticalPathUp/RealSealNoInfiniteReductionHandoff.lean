import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealSealNoInfiniteReductionHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              Cont realSeal localName sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row realSeal ∨ hsame row obstruction ∨
                          hsame row dischargeSocket ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory sealRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal realSealLocalNameRead sealReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed realSealUnary localNameUnary realSealLocalNameRead
  have sourceSealRead :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row realSeal ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSealRead
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealReadPkg, provenancePkg⟩
  }
  exact ⟨cert, sealReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
