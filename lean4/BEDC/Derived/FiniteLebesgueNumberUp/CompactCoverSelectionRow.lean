import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactCoverSelectionRow [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow coverRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius coverRead ->
        Cont coverRead mesh compactRead ->
          PkgSig bundle compactRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row coverRead ∨ hsame row compactRead ∨
                    Cont coverRead mesh compactRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                    hsame row compactRead)
                hsame ∧
              UnaryHistory coverRead ∧ UnaryHistory compactRead ∧
                Cont cover radius coverRead ∧ Cont coverRead mesh compactRead ∧
                  PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier coverRadiusRead readMeshCompact compactPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusRead
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed coverReadUnary meshUnary readMeshCompact
  have sourceCompact :
      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row) compactRead := by
    exact ⟨hsame_refl compactRead, compactReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverRead ∨ hsame row compactRead ∨ Cont coverRead mesh compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead sourceCompact
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, compactPkg, source.left⟩
  }
  exact
    ⟨cert, coverReadUnary, compactReadUnary, coverRadiusRead, readMeshCompact,
      compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
