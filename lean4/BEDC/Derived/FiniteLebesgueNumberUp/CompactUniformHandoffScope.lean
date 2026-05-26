import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactUniformHandoffScope [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead selectorRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius compactRead →
        Cont compactRead mesh selectorRead →
          Cont selectorRead route uniformRead →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactRead ∨ hsame row selectorRead ∨ hsame row uniformRead)
                  (fun row : BHist =>
                    hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory selectorRead ∧
                  UnaryHistory uniformRead ∧ Cont cover window radius ∧
                    Cont cover radius compactRead ∧ Cont compactRead mesh selectorRead ∧
                      Cont selectorRead route uniformRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusCompact compactMeshSelector selectorRouteUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusCompact
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed compactUnary meshUnary compactMeshSelector
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed selectorUnary routeUnary selectorRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactRead ∨ hsame row selectorRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact
    ⟨cert, compactUnary, selectorUnary, uniformUnary, coverWindowRadius, coverRadiusCompact,
      compactMeshSelector, selectorRouteUniform, provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
