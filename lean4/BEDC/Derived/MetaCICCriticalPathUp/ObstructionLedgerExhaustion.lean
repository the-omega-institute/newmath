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

theorem MetaCICCriticalPathPacket_obstruction_ledger_exhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff obstruction socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => (hsame row obstruction ∨ hsame row socketRead) ∧
                UnaryHistory row)
              (fun row : BHist =>
                hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row socketRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ hsame transport localName)
              hsame ∧
            UnaryHistory obstruction ∧ UnaryHistory socketRead ∧
              Cont handoff obstruction socketRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffObstructionRead _socketReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have sourceObstruction :
      (fun row : BHist => (hsame row obstruction ∨ hsame row socketRead) ∧
        UnaryHistory row) obstruction := by
    exact ⟨Or.inl (hsame_refl obstruction), obstructionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row obstruction ∨ hsame row socketRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ hsame transport localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstruction sourceObstruction
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        constructor
        · cases source.left with
          | inl sameObstruction =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction)
          | inr sameSocketRead =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSocketRead)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameObstruction =>
          exact Or.inl sameObstruction
      | inr sameSocketRead =>
          exact Or.inr (Or.inr sameSocketRead)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, transportLocalName⟩
  }
  exact ⟨cert, obstructionUnary, socketReadUnary, handoffObstructionRead, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
