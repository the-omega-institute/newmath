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

theorem MetaCICCriticalPathFourFaceSocketSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal admitted socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName dyadicBudget ->
        Cont dyadicBudget route streamSchedule ->
          Cont streamSchedule normalForm regReadback ->
            Cont regReadback provenance realSeal ->
              Cont realSeal localName admitted ->
                Cont admitted dischargeSocket socketRead ->
                  PkgSig bundle admitted pkg ->
                    PkgSig bundle socketRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row admitted ∨ hsame row socketRead)
                          (fun row : BHist =>
                            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                              hsame row regReadback ∨ hsame row realSeal ∨
                                hsame row admitted ∨ hsame row dischargeSocket ∨
                                  hsame row socketRead)
                          (fun row : BHist =>
                            PkgSig bundle row pkg ∧
                              (hsame row admitted ∨ hsame row socketRead))
                          hsame ∧
                        UnaryHistory admitted ∧ UnaryHistory socketRead ∧
                          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalBudget budgetRouteStream streamNormalReadback readbackProvenanceSeal
    sealLocalAdmitted admittedSocketRead admittedPkg socketReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteStream
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary streamNormalReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed realSealUnary localNameUnary sealLocalAdmitted
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed admittedUnary dischargeSocketUnary admittedSocketRead
  have sourceAdmitted :
      (fun row : BHist => hsame row admitted ∨ hsame row socketRead) admitted := by
    exact Or.inl (hsame_refl admitted)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admitted ∨ hsame row socketRead)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal ∨ hsame row admitted ∨
                hsame row dischargeSocket ∨ hsame row socketRead)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ (hsame row admitted ∨ hsame row socketRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro admitted sourceAdmitted
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameAdmitted =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameAdmitted))))
      | inr sameSocketRead =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSocketRead)))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameAdmitted =>
          cases sameAdmitted
          exact ⟨admittedPkg, Or.inl (hsame_refl admitted)⟩
      | inr sameSocketRead =>
          cases sameSocketRead
          exact ⟨socketReadPkg, Or.inr (hsame_refl socketRead)⟩
  }
  exact ⟨cert, admittedUnary, socketReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
