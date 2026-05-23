import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_pointwise_radius_route [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName pointwiseRead radiusRead selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont radii moduli pointwiseRead ->
        Cont pointwiseRead fold radiusRead ->
          Cont radiusRead precision selectedRead ->
            PkgSig bundle selectedRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    CompactNetModulusSelectorCarrier source target tolerance probes centers
                        radii moduli fold precision transport route provenance localName
                        bundle pkg ∧
                      hsame row selectedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (hsame row pointwiseRead ∨ hsame row radiusRead ∨
                        hsame row selectedRead))
                  (fun _row : BHist =>
                    Cont radii moduli pointwiseRead ∧ Cont pointwiseRead fold radiusRead ∧
                      Cont radiusRead precision selectedRead ∧ PkgSig bundle selectedRead pkg)
                  hsame ∧
                UnaryHistory pointwiseRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory selectedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier radiiModuliPointwise pointwiseFoldRadius radiusPrecisionSelected
    selectedReadPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _targetUnary, _toleranceUnary, _probesUnary, _centersUnary,
    radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed radiiUnary moduliUnary radiiModuliPointwise
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed pointwiseReadUnary foldUnary pointwiseFoldRadius
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed radiusReadUnary precisionUnary radiusPrecisionSelected
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CompactNetModulusSelectorCarrier source target tolerance probes centers radii
                moduli fold precision transport route provenance localName bundle pkg ∧
              hsame row selectedRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row pointwiseRead ∨ hsame row radiusRead ∨ hsame row selectedRead))
          (fun _row : BHist =>
            Cont radii moduli pointwiseRead ∧ Cont pointwiseRead fold radiusRead ∧
              Cont radiusRead precision selectedRead ∧ PkgSig bundle selectedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectedRead
        ⟨carrierWitness, hsame_refl selectedRead⟩
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
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨unary_transport selectedReadUnary (hsame_symm sourceRow.right),
        Or.inr (Or.inr sourceRow.right)⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨radiiModuliPointwise, pointwiseFoldRadius, radiusPrecisionSelected,
          selectedReadPkg⟩
  }
  exact ⟨cert, pointwiseReadUnary, radiusReadUnary, selectedReadUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
