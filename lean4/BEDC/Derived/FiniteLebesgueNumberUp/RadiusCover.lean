import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberUniformConsumerRadiusCover [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow sourceRead compactRead
      uniformRead radiusCover : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window sourceRead ->
        Cont sourceRead radius compactRead ->
          Cont compactRead route uniformRead ->
            Cont radius uniformRead radiusCover ->
              PkgSig bundle radiusCover pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row radiusCover ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sourceRead ∨ hsame row compactRead ∨
                        hsame row uniformRead ∨ hsame row radiusCover)
                    (fun row : BHist =>
                      hsame row radiusCover ∧ PkgSig bundle radiusCover pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory compactRead ∧
                    UnaryHistory uniformRead ∧ UnaryHistory radiusCover := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverWindowSource sourceRadiusCompact compactRouteUniform
    radiusUniformCover radiusCoverPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary radiusUnary sourceRadiusCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary routeUnary compactRouteUniform
  have radiusCoverUnary : UnaryHistory radiusCover :=
    unary_cont_closed radiusUnary uniformUnary radiusUniformCover
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row radiusCover ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row compactRead ∨
              hsame row uniformRead ∨ hsame row radiusCover)
          (fun row : BHist => hsame row radiusCover ∧ PkgSig bundle radiusCover pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro radiusCover ⟨hsame_refl radiusCover, radiusCoverUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, radiusCoverPkg⟩
  }
  exact ⟨cert, sourceUnary, compactUnary, uniformUnary, radiusCoverUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
