import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNeutralSpineDecidabilityHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal neutralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction neutralRead ->
        Cont route localName dyadicBudget ->
          Cont dyadicBudget route streamSchedule ->
            Cont streamSchedule normalForm regReadback ->
              Cont regReadback provenance realSeal ->
                PkgSig bundle neutralRead pkg ->
                  PkgSig bundle realSeal pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row neutralRead ∨ hsame row dyadicBudget ∨
                            hsame row streamSchedule ∨ hsame row regReadback ∨
                              hsame row realSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle neutralRead pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory neutralRead ∧ UnaryHistory realSeal ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffObstructionNeutral routeLocalNameBudget budgetRouteSchedule
    scheduleNormalFormReadback readbackProvenanceSeal neutralReadPkg realSealPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have neutralReadUnary : UnaryHistory neutralRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionNeutral
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row neutralRead ∨ hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle neutralRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact ⟨source.right, neutralReadPkg, realSealPkg⟩
  }
  exact ⟨cert, neutralReadUnary, realSealUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
