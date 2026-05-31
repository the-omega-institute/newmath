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

theorem MetaCICCriticalPathPhaseRealRootUnblockAdmission [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName dyadicBudget ->
        Cont dyadicBudget route streamSchedule ->
          Cont streamSchedule normalForm regReadback ->
            Cont regReadback provenance realSeal ->
              Cont realSeal localName admitted ->
                PkgSig bundle admitted pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row admitted ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                          hsame row regReadback ∨ hsame row realSeal ∨
                            hsame row admitted)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle admitted pkg)
                      hsame ∧
                    UnaryHistory admitted ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalDyadic dyadicRouteStream streamNormalReg regProvenanceReal
    realLocalAdmitted admittedPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalDyadic
  have streamUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicUnary routeUnary dyadicRouteStream
  have regUnary : UnaryHistory regReadback :=
    unary_cont_closed streamUnary normalFormUnary streamNormalReg
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regUnary provenanceUnary regProvenanceReal
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed realUnary localNameUnary realLocalAdmitted
  have sourceAdmitted :
      (fun row : BHist => hsame row admitted ∧ UnaryHistory row) admitted := by
    exact ⟨hsame_refl admitted, admittedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admitted ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal ∨ hsame row admitted)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle admitted pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, admittedPkg⟩
  }
  exact ⟨cert, admittedUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
