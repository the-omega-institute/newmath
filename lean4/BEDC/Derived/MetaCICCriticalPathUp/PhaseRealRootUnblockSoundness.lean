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

theorem MetaCICCriticalPathPhaseRealRootUnblockSoundness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal admitted sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              Cont realSeal localName admitted →
                Cont admitted provenance sourceRead →
                  PkgSig bundle admitted pkg →
                    PkgSig bundle sourceRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                              hsame row regReadback ∨ hsame row realSeal ∨
                                hsame row admitted ∨ hsame row sourceRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧
                              PkgSig bundle provenance pkg)
                          hsame ∧
                        UnaryHistory sourceRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalBudget budgetRouteStream streamNormalReadback
    readbackProvenanceSeal sealLocalAdmitted admittedProvenanceSource _admittedPkg
    sourceReadPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed admittedUnary provenanceUnary admittedProvenanceSource
  have sourceSourceRead :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regReadback ∨
              hsame row realSeal ∨ hsame row admitted ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceSourceRead
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
      exact ⟨source.right, sourceReadPkg, provenancePkg⟩
  }
  exact ⟨cert, sourceReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
