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

theorem MetaCICCriticalPathL10FourFaceObligationNoncollapse [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              Cont dyadicBudget realSeal obligationRead →
                PkgSig bundle obligationRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                          hsame row regReadback ∨ hsame row realSeal ∨
                            hsame row obligationRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle obligationRead pkg ∧
                          Cont dyadicBudget realSeal obligationRead)
                      hsame ∧
                    UnaryHistory dyadicBudget ∧ UnaryHistory streamSchedule ∧
                      UnaryHistory regReadback ∧ UnaryHistory realSeal ∧
                        UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal budgetRealSealObligation obligationPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicUnary routeUnary budgetRouteSchedule
  have readbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary provenanceUnary readbackProvenanceSeal
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed dyadicUnary realSealUnary budgetRealSealObligation
  have sourceObligation :
      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          obligationRead := by
    exact ⟨hsame_refl obligationRead, obligationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle obligationRead pkg ∧
              Cont dyadicBudget realSeal obligationRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead sourceObligation
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
      exact ⟨source.right, obligationPkg, budgetRealSealObligation⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, readbackUnary, realSealUnary, obligationUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
