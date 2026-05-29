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

theorem MetaCICCriticalPathPacket_root_route_totality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalRead socketRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm normalRead →
        Cont handoff obstruction socketRead →
          Cont normalRead socketRead rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                      hsame row dischargeSocket ∨ hsame row rootRead)
                  (fun row : BHist =>
                    hsame row rootRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory normalRead ∧ UnaryHistory socketRead ∧
                  UnaryHistory rootRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalRead handoffSocketRead normalSocketRootRead rootReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalRead
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffSocketRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed normalReadUnary socketReadUnary normalSocketRootRead
  have sourceRootRead :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row dischargeSocket ∨ hsame row rootRead)
          (fun row : BHist =>
            hsame row rootRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRootRead
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
      exact ⟨source.left, provenancePkg, rootReadPkg⟩
  }
  exact ⟨cert, normalReadUnary, socketReadUnary, rootReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
