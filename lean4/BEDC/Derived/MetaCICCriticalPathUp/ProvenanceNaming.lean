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

theorem MetaCICCriticalPathPacket_provenance_naming [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName provenanceRead namingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont provenance localName provenanceRead ->
        Cont provenanceRead localName namingRead ->
          PkgSig bundle namingRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row provenanceRead ∨ hsame row namingRead ∨
                    hsame row provenance ∨ hsame row localName) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row provenance ∨ hsame row localName ∨
                    hsame row provenanceRead ∨ hsame row namingRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle namingRead pkg)
                hsame ∧
              UnaryHistory provenanceRead ∧ UnaryHistory namingRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet provenanceRoute namingRoute namingPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceRoute
  have namingReadUnary : UnaryHistory namingRead :=
    unary_cont_closed provenanceReadUnary localNameUnary namingRoute
  have sourceNaming :
      (fun row : BHist =>
        (hsame row provenanceRead ∨ hsame row namingRead ∨ hsame row provenance ∨
          hsame row localName) ∧ UnaryHistory row) namingRead := by
    exact ⟨Or.inr (Or.inl (hsame_refl namingRead)), namingReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row provenanceRead ∨ hsame row namingRead ∨ hsame row provenance ∨
              hsame row localName) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row localName ∨ hsame row provenanceRead ∨
              hsame row namingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle namingRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namingRead sourceNaming
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
          | inl sameProvenanceRead =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameProvenanceRead)
          | inr rest =>
              cases rest with
              | inl sameNamingRead =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNamingRead))
              | inr rest =>
                  cases rest with
                  | inl sameProvenance =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameProvenance)))
                  | inr sameLocalName =>
                      exact Or.inr (Or.inr
                        (Or.inr (hsame_trans (hsame_symm sameRows) sameLocalName)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameProvenanceRead =>
          exact Or.inr (Or.inr (Or.inl sameProvenanceRead))
      | inr rest =>
          cases rest with
          | inl sameNamingRead =>
              exact Or.inr (Or.inr (Or.inr sameNamingRead))
          | inr rest =>
              cases rest with
              | inl sameProvenance => exact Or.inl sameProvenance
              | inr sameLocalName => exact Or.inr (Or.inl sameLocalName)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namingPkg⟩
  }
  exact ⟨cert, provenanceReadUnary, namingReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
