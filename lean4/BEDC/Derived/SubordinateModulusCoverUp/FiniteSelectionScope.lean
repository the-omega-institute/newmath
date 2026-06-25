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

theorem SubordinateModulusCoverFiniteSelectionScope [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name selectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont bundleSpine centers selectionRead →
        PkgSig bundle selectionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row selectionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
                  hsame row precision ∨ hsame row coverage ∨ hsame row comparisons ∨
                    hsame row selectionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont bundleSpine centers selectionRead ∧
                  PkgSig bundle selectionRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory selectionRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier bundleCentersRead selectionPkg
  obtain ⟨_eUnary, bundleSpineUnary, centersUnary, _radiiUnary, _precisionUnary,
    _pointwiseUnary, _coverageUnary, _comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _coverageRoute, _comparisonRoute, provenancePkg,
    _namePkg⟩ := carrier
  have selectionUnary : UnaryHistory selectionRead :=
    unary_cont_closed bundleSpineUnary centersUnary bundleCentersRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row coverage ∨ hsame row comparisons ∨
                hsame row selectionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bundleSpine centers selectionRead ∧
              PkgSig bundle selectionRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectionRead ⟨hsame_refl selectionRead, selectionUnary⟩
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
      exact ⟨source.right, bundleCentersRead, selectionPkg, provenancePkg⟩
  }
  exact ⟨cert, selectionUnary, provenancePkg⟩

end BEDC.Derived.SubordinateModulusCoverUp
