import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_rational_scalar_bridge_boundary [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint realSeal bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      hsame realSeal readback ->
        Cont endpoint realSeal bridgeRead ->
          PkgSig bundle bridgeRead pkg ->
            UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
              UnaryHistory scaledEndpoint ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                UnaryHistory bridgeRead ∧ Cont scalar window scalarEndpoint ∧
                  Cont source window sourceEndpoint ∧
                    Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                      Cont scaledEndpoint budget readback ∧ Cont endpoint realSeal bridgeRead ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameRealSeal endpointRealSealBridge bridgePkg
  obtain ⟨scalarUnary, sourceUnary, windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, scaledEndpointUnary, _budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, endpointUnary, scalarWindow, sourceWindow,
    endpointsScaled, scaledBudgetReadback, _readbackRoute, _provenanceNamecert,
    _sameRowsAppend, endpointPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_transport readbackUnary (hsame_symm sameRealSeal)
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealBridge
  exact
    ⟨scalarUnary, sourceUnary, windowUnary, scaledEndpointUnary, readbackUnary,
      realSealUnary, bridgeReadUnary, scalarWindow, sourceWindow, endpointsScaled,
      scaledBudgetReadback, endpointRealSealBridge, endpointPkg, bridgePkg⟩

theorem RegularCauchyScaleCarrier_public_consumer_boundary [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      Cont endpoint readback publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row scalar ∨ hsame row source ∨ hsame row window ∨
                  hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback ∨
                    hsame row endpoint ∨ hsame row publicRead)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead ∧ Cont endpoint readback publicRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointReadbackPublic publicPkg
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, _budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, endpointUnary, _scalarWindow,
    _sourceWindow, _endpointsScaled, _scaledBudget, _readbackRoute, _provenanceNamecert,
    _sameRowsAppend, endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackPublic
  have sourcePublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scalar ∨ hsame row source ∨ hsame row window ∨
              hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback ∨
                hsame row endpoint ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows'
        exact hsame_symm sameRows'
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows' sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows') sourceRow.left,
            unary_transport sourceRow.right sameRows'⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, publicPkg⟩
  }
  exact ⟨cert, publicUnary, endpointReadbackPublic, endpointPkg, publicPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
