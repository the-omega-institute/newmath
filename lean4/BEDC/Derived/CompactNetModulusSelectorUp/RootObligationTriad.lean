import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorRootObligationTriad [AskSetup] [PackageSetup]
    {source target tolerance centers coverage radius pointwise fold precision transport route
      provenance localName rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance centers coverage radius
        pointwise fold precision transport route provenance localName bundle pkg ->
      Cont route localName rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row centers ∨ hsame row coverage ∨
                  hsame row radius ∨ hsame row pointwise ∨ hsame row fold ∨
                    hsame row precision ∨ hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont route localName rootRead ∧
                  PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier rootRoute rootPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, centersUnary, coverageUnary,
    _radiusUnary, pointwiseUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, localNameUnary, _carrierSourceCentersCoverage,
    _carrierPointwiseFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ :=
    carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary localNameUnary rootRoute
  have sourceAtRoot :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row centers ∨ hsame row coverage ∨
              hsame row radius ∨ hsame row pointwise ∨ hsame row fold ∨
                hsame row precision ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName rootRead ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceAtRoot
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootRoute, rootPkg⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
