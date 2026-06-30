import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathNormalizationFrontierConsumerRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName normalRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont strongNorm normalForm normalRead ->
        Cont normalRead handoff l10Read ->
          PkgSig bundle l10Read pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row l10Read)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont strongNorm normalForm normalRead ∧
                    Cont normalRead handoff l10Read ∧ PkgSig bundle l10Read pkg ∧
                      PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet normalRoute l10Route l10Pkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed strongNormUnary normalFormUnary normalRoute
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed normalUnary handoffUnary l10Route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm normalRead ∧
              Cont normalRead handoff l10Read ∧ PkgSig bundle l10Read pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Read ⟨hsame_refl l10Read, l10Unary⟩
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
      exact ⟨source.right, normalRoute, l10Route, l10Pkg, provenancePkg⟩
  }
  exact ⟨cert, normalUnary, l10Unary⟩

end BEDC.Derived.MetaCICCriticalPathUp
