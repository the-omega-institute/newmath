import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPositiveRadiusTotality [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius compactRead ->
        PkgSig bundle compactRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row radius ∨ hsame row compactRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                  hsame row compactRead)
              hsame ∧
            UnaryHistory radius ∧ UnaryHistory compactRead ∧ Cont window radius compactRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowRadiusRead compactPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have sourceCompact :
      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row) compactRead := by
    exact ⟨hsame_refl compactRead, compactUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row radius ∨ hsame row compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compactRead sourceCompact
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
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, compactPkg, source.left⟩
    }
  exact ⟨cert, radiusUnary, compactUnary, windowRadiusRead, provenancePkg, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
