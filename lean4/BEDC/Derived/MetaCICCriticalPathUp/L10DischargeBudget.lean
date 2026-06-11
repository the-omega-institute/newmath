import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10DischargeBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regSeqReadback realSeal exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regSeqReadback →
            Cont regSeqReadback provenance realSeal →
              Cont dischargeSocket realSeal exitRead →
                PkgSig bundle exitRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dischargeSocket ∨ hsame row dyadicBudget ∨
                          hsame row streamSchedule ∨ hsame row regSeqReadback ∨
                            hsame row realSeal ∨ hsame row exitRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle exitRead pkg ∧
                          Cont dischargeSocket realSeal exitRead)
                      hsame ∧
                    UnaryHistory dischargeSocket ∧ UnaryHistory exitRead := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameDyadic dyadicRouteStream streamNormalFormReadback
    readbackProvenanceReal dischargeRealExit exitPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionDischargeSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameDyadic
  have streamUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicUnary routeUnary dyadicRouteStream
  have regSeqUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed streamUnary normalFormUnary streamNormalFormReadback
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqUnary provenanceUnary readbackProvenanceReal
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed dischargeSocketUnary realUnary dischargeRealExit
  have sourceExit :
      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row) exitRead := by
    exact ⟨hsame_refl exitRead, exitUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dischargeSocket ∨ hsame row dyadicBudget ∨
              hsame row streamSchedule ∨ hsame row regSeqReadback ∨
                hsame row realSeal ∨ hsame row exitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle exitRead pkg ∧
              Cont dischargeSocket realSeal exitRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exitRead sourceExit
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
      exact ⟨source.right, exitPkg, dischargeRealExit⟩
  }
  exact ⟨cert, dischargeSocketUnary, exitUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
