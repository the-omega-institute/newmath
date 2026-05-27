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

theorem MetaCICCriticalPathPacket_normal_form_route_coverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName readback →
        PkgSig bundle readback pkg →
          SemanticNameCert
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row readback)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont strongNorm normalForm route ∧
                  Cont route localName readback ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameReadback _readbackPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameReadback
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm route ∧
              Cont route localName readback ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, strongNormNormalFormRoute, routeLocalNameReadback, provenancePkg⟩
  }
  exact ⟨cert, readbackUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
