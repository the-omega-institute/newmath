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

theorem MetaCICCriticalPathPacket_bounded_checker_handoff_totality
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName checkerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont handoff route checkerRead →
        PkgSig bundle checkerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row handoff ∨ hsame row route ∨ hsame row checkerRead ∨
                  hsame row dischargeSocket)
              (fun row : BHist =>
                hsame row checkerRead ∧ Cont handoff route checkerRead ∧
                  PkgSig bundle checkerRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory checkerRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet handoffRouteRead checkerReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have checkerReadUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteRead
  have sourceCheckerRead :
      (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row) checkerRead := by
    exact ⟨hsame_refl checkerRead, checkerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row route ∨ hsame row checkerRead ∨
              hsame row dischargeSocket)
          (fun row : BHist =>
            hsame row checkerRead ∧ Cont handoff route checkerRead ∧
              PkgSig bundle checkerRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro checkerRead sourceCheckerRead
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffRouteRead, checkerReadPkg, provenancePkg⟩
  }
  exact ⟨cert, checkerReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
