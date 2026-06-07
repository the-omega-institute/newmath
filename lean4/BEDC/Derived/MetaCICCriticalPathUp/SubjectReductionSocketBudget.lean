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

theorem MetaCICCriticalPathSubjectReductionSocketBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName consistencyRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont strongNorm normalForm consistencyRead ->
        Cont handoff obstruction socketRead ->
          PkgSig bundle socketRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row consistencyRead ∨ hsame row socketRead ∨
                    hsame row dischargeSocket) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row dischargeSocket ∨
                      hsame row consistencyRead ∨ hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
                    PkgSig bundle socketRead pkg ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory consistencyRead ∧ UnaryHistory socketRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet strongNormNormalFormConsistency handoffObstructionSocket socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionDischargeSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormConsistency
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary _obstructionUnary handoffObstructionSocket
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row consistencyRead ∨ hsame row socketRead ∨
              hsame row dischargeSocket) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨
                hsame row consistencyRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consistencyRead
          ⟨Or.inl (hsame_refl consistencyRead), consistencyUnary⟩
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
        constructor
        · cases source.left with
          | inl consistencySame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) consistencySame)
          | inr rest =>
              cases rest with
              | inl socketSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) socketSame))
              | inr dischargeSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) dischargeSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl consistencySame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl consistencySame)))))
      | inr rest =>
          cases rest with
          | inl socketSame =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr socketSame)))))
          | inr dischargeSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl dischargeSame))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffObstructionSocket, socketPkg, provenancePkg⟩
  }
  exact ⟨cert, consistencyUnary, socketUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
