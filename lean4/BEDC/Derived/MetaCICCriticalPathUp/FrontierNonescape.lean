import BEDC.Derived.MetaCICCriticalPathUp.RouteLedgerTotality

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFrontierSlice_nonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName query consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierSlice strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName query bundle pkg →
      Cont route query consumerRead →
        PkgSig bundle consumerRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row obstruction ∨ hsame row dischargeSocket ∨
                  hsame row consumerRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row route ∨
                  hsame row query ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle query pkg ∧ PkgSig bundle consumerRead pkg)
              hsame ∧
            UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert UnaryHistory ProbeBundle Pkg
  intro slice routeQueryConsumer consumerReadPkg
  obtain ⟨packet, queryUnary, queryPkg⟩ := slice
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed routeUnary queryUnary routeQueryConsumer
  have sourceObstruction :
      (fun row : BHist =>
        (hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row consumerRead) ∧
          UnaryHistory row) obstruction := by
    exact ⟨Or.inl (hsame_refl obstruction), obstructionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row consumerRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row route ∨
              hsame row query ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle query pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstruction sourceObstruction
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
          | inl sameObstruction =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObstruction)
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
              | inr sameConsumer =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameConsumer))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameObstruction =>
          exact Or.inl sameObstruction
      | inr rest =>
          cases rest with
          | inl sameSocket =>
              exact Or.inr (Or.inl sameSocket)
          | inr sameConsumer =>
              exact Or.inr (Or.inr (Or.inr (Or.inr sameConsumer)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, queryPkg, consumerReadPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
