import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberUniformModulusRadiusScope [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius route uniformRead →
        PkgSig bundle uniformRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row radius ∨ hsame row uniformRead ∨ Cont radius route uniformRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                  hsame row uniformRead)
              hsame ∧
            UnaryHistory radius ∧ UnaryHistory uniformRead ∧
              Cont radius route uniformRead ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusRouteUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed radiusUnary routeUnary radiusRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row uniformRead ∨ Cont radius route uniformRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              hsame row uniformRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inl source.left)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, uniformPkg, source.left⟩
    }
  exact ⟨cert, radiusUnary, uniformUnary, radiusRouteUniform, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
