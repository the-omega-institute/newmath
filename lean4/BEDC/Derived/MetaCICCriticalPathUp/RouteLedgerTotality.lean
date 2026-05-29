import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathFrontierSlice [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName query : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
      route provenance localName bundle pkg ∧
    UnaryHistory query ∧ PkgSig bundle query pkg

theorem MetaCICCriticalPathFrontierSlice_route_ledger_totality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName query : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierSlice strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName query bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row route ∨ hsame row dischargeSocket ∨ hsame row query) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row query)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle query pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory PkgSig
  intro slice
  obtain ⟨packet, queryUnary, queryPkg⟩ := slice
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have routeSource :
      (fun row : BHist =>
        (hsame row route ∨ hsame row dischargeSocket ∨ hsame row query) ∧
          UnaryHistory row) route := by
    exact ⟨Or.inl (hsame_refl route), routeUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro route routeSource
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
          | inl routeSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) routeSame)
          | inr rest =>
              cases rest with
              | inl socketSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) socketSame))
              | inr querySame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) querySame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl routeSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl routeSame))))))
      | inr rest =>
          cases rest with
          | inl socketSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl socketSame))))
          | inr querySame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr querySame))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, queryPkg⟩
  }

end BEDC.Derived.MetaCICCriticalPathUp
