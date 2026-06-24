import BEDC.Derived.SubordinateModulusCoverUp.TasteGate

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubordinateModulusCoverScopeDependency [AskSetup] [PackageSetup]
    {tolerance bundleRow centers radii precision pointwise coverage comparisons transport route
      provenance localName compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier tolerance bundleRow centers radii precision pointwise coverage
        comparisons transport route provenance localName bundle pkg →
      Cont compactRead uniformRead route →
        PkgSig bundle provenance pkg →
          SemanticNameCert
              (fun row : BHist => hsame row route ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row bundleRow ∨ hsame row centers ∨ hsame row radii ∨
                  hsame row precision ∨ hsame row coverage ∨ hsame row comparisons ∨
                    hsame row route)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compactRead uniformRead route ∧
                  PkgSig bundle provenance pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactUniformRoute provenancePkgInput
  obtain ⟨_toleranceUnary, _bundleUnary, _centersUnary, _radiiUnary, _precisionUnary,
    _pointwiseUnary, _coverageUnary, _comparisonsUnary, _transportUnary, routeUnary,
    _provenanceUnary, _localNameUnary, _coverageRoute, _comparisonRoute, provenancePkg,
      _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundleRow ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row coverage ∨ hsame row comparisons ∨
                hsame row route)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactRead uniformRead route ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route ⟨hsame_refl route, routeUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactUniformRoute, provenancePkgInput⟩
  }
  have _carrierProvenance : PkgSig bundle provenance pkg := provenancePkg
  exact cert

end BEDC.Derived.SubordinateModulusCoverUp
