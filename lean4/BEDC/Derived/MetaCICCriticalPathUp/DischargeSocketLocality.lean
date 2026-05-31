import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_discharge_socket_locality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      hsame socketRead dischargeSocket →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
                  hsame row localName)
              (fun row : BHist =>
                hsame row socketRead ∧ PkgSig bundle socketRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socketRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory PkgSig
  intro packet socketReadDischarge socketPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_transport dischargeSocketUnary (hsame_symm socketReadDischarge)
  have sourceSocketRead :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dischargeSocket ∨ hsame row transport ∨ hsame row route ∨
              hsame row localName)
          (fun row : BHist =>
            hsame row socketRead ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocketRead
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
      exact Or.inl (hsame_trans source.left socketReadDischarge)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, socketPkg, provenancePkg⟩
  }
  exact ⟨cert, socketReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
