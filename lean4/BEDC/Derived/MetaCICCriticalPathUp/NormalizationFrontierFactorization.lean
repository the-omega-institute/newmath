import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_normalization_frontier_factorization
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm normalRead →
        hsame obstructionRead obstruction →
          PkgSig bundle normalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨
                    hsame row obstructionRead ∨ hsame row normalRead)
                (fun row : BHist =>
                  hsame row normalRead ∧ PkgSig bundle normalRead pkg ∧
                    hsame obstructionRead obstruction ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory normalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet strongNormNormalRead obstructionReadObstruction normalReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalRead
  have sourceNormalRead :
      (fun row : BHist => hsame row normalRead ∧ UnaryHistory row) normalRead := by
    exact ⟨hsame_refl normalRead, normalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstructionRead ∨
              hsame row normalRead)
          (fun row : BHist =>
            hsame row normalRead ∧ PkgSig bundle normalRead pkg ∧
              hsame obstructionRead obstruction ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead sourceNormalRead
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
      exact ⟨source.left, normalReadPkg, obstructionReadObstruction, provenancePkg⟩
  }
  exact ⟨cert, normalReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
