import BEDC.Derived.SubordinateModulusCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubordinateModulusCoverCompactUniformConsumerBoundary [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont bundleSpine coverage compactRead →
        Cont compactRead comparisons uniformRead →
          PkgSig bundle uniformRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row bundleSpine ∨ hsame row pointwise ∨ hsame row comparisons ∨
                    hsame row coverage ∨ hsame row uniformRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont bundleSpine coverage compactRead ∧
                    Cont compactRead comparisons uniformRead ∧ PkgSig bundle uniformRead pkg)
                hsame ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier bundleCoverageRead compactComparisonRead uniformPkg
  obtain ⟨_eUnary, bundleSpineUnary, _centersUnary, _radiiUnary, _precisionUnary,
    _pointwiseUnary, coverageUnary, comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _coverageRoute, _comparisonRoute, _provenancePkg,
    _namePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleSpineUnary coverageUnary bundleCoverageRead
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary comparisonsUnary compactComparisonRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundleSpine ∨ hsame row pointwise ∨ hsame row comparisons ∨
              hsame row coverage ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bundleSpine coverage compactRead ∧
              Cont compactRead comparisons uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bundleCoverageRead, compactComparisonRead, uniformPkg⟩
  }
  exact ⟨cert, compactUnary, uniformUnary⟩

end BEDC.Derived.SubordinateModulusCoverUp
