import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.Derived.MetaCICCriticalPathUp.ResidualSubstitutionNormalizationFrontier

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathDiamondBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance localName
      residualRead normalizationRead frontierRead checkerRead decidabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont handoff route residualRead → Cont strongNorm normalForm normalizationRead →
        Cont residualRead normalizationRead frontierRead →
          Cont frontierRead transport checkerRead →
            Cont checkerRead handoff decidabilityRead → PkgSig bundle frontierRead pkg →
              PkgSig bundle checkerRead pkg → SemanticNameCert
                (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row residualRead ∨ hsame row normalizationRead ∨
                    hsame row frontierRead ∨ hsame row checkerRead ∨
                      hsame row decidabilityRead ∨ hsame row dischargeSocket)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle frontierRead pkg ∧ PkgSig bundle checkerRead pkg)
                hsame ∧ UnaryHistory residualRead ∧ UnaryHistory normalizationRead ∧
                  UnaryHistory frontierRead ∧ UnaryHistory checkerRead ∧
                    UnaryHistory decidabilityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet residualRoute normalizationRoute frontierRoute checkerRoute decidabilityRoute
    frontierPkg checkerPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary routeUnary residualRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary normalizationRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed residualUnary normalizationUnary frontierRoute
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed frontierUnary transportUnary checkerRoute
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed checkerUnary handoffUnary decidabilityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row residualRead ∨ hsame row normalizationRead ∨
              hsame row frontierRead ∨ hsame row checkerRead ∨
                hsame row decidabilityRead ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle frontierRead pkg ∧ PkgSig bundle checkerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro decidabilityRead
        ⟨hsame_refl decidabilityRead, decidabilityUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, frontierPkg, checkerPkg⟩
  }
  exact
    ⟨cert, residualUnary, normalizationUnary, frontierUnary, checkerUnary,
      decidabilityUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
