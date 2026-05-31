import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusModulusTransportScope [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow selectorRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh selectorRead ->
        Cont selectorRead route uniformRead ->
          PkgSig bundle uniformRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row radius ∨ hsame row selectorRead ∨ hsame row uniformRead)
                (fun row : BHist =>
                  hsame row radius ∨ Cont radius mesh selectorRead ∨
                    Cont selectorRead route uniformRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                    (hsame row radius ∨ hsame row selectorRead ∨ hsame row uniformRead))
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory selectorRead ∧ UnaryHistory uniformRead ∧
                Cont radius mesh selectorRead ∧ Cont selectorRead route uniformRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier radiusMeshSelector selectorRouteUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshSelector
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed selectorUnary routeUnary selectorRouteUniform
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row radius ∨ hsame row selectorRead ∨ hsame row uniformRead)
          (fun row : BHist =>
            hsame row radius ∨ Cont radius mesh selectorRead ∨
              Cont selectorRead route uniformRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              (hsame row radius ∨ hsame row selectorRead ∨ hsame row uniformRead))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead (Or.inr (Or.inr (hsame_refl uniformRead)))
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
          cases sourceRow with
          | inl sameRadius =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRadius)
          | inr tail =>
              cases tail with
              | inl sameSelector =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSelector))
              | inr sameUniform =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameUniform))
      }
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow with
        | inl sameRadius =>
            exact Or.inl sameRadius
        | inr tail =>
            cases tail with
            | inl _sameSelector =>
                exact Or.inr (Or.inl radiusMeshSelector)
            | inr _sameUniform =>
                exact Or.inr (Or.inr selectorRouteUniform)
      ledger_sound := by
        intro _row sourceRow
        cases sourceRow with
        | inl sameRadius =>
            exact ⟨provenancePkg, uniformPkg, Or.inl sameRadius⟩
        | inr tail =>
            cases tail with
            | inl _sameSelector =>
                exact ⟨provenancePkg, uniformPkg, Or.inr (Or.inl _sameSelector)⟩
            | inr sameUniform =>
                exact ⟨provenancePkg, uniformPkg, Or.inr (Or.inr sameUniform)⟩
    }
  exact
    ⟨cert, radiusUnary, selectorUnary, uniformUnary, radiusMeshSelector, selectorRouteUniform,
      provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
