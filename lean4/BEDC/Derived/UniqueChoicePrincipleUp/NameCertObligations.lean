import BEDC.Derived.UniqueChoicePrincipleUp.DeterministicReadback
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniqueChoicePrincipleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniqueChoicePrincipleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source relation existence uniqueness deterministic transport replay provenance localName
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniqueChoicePrincipleCarrier source relation existence uniqueness deterministic transport
        replay provenance localName bundle pkg ->
      Cont deterministic transport readback ->
        PkgSig bundle readback pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row deterministic ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row localName)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle readback pkg)
              hsame ∧
            UnaryHistory readback ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier deterministicTransportReadback readbackPkg
  obtain ⟨_sourceUnary, _relationUnary, _existenceUnary, _uniquenessUnary,
    deterministicUnary, transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _sourceRelationExistence, _existenceUniquenessDeterministic,
    deterministicTransportReplay, _replayProvenanceLocalName, provenancePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed deterministicUnary transportUnary deterministicTransportReadback
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row deterministic ∨ hsame row transport ∨ hsame row replay ∨
              hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle readback pkg)
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inl
              (hsame_trans sourceRow.left
                (cont_respects_hsame (hsame_refl deterministic) (hsame_refl transport)
                  deterministicTransportReadback deterministicTransportReplay))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, readbackPkg⟩
  }
  exact ⟨cert, readbackUnary, provenancePkg⟩

end BEDC.Derived.UniqueChoicePrincipleUp
