import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_real_seal_handoff_obligation [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      Cont readback endpoint sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row readback ∨ hsame row endpoint ∨ hsame row sealRead)
              (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
              hsame ∧
            UnaryHistory readback ∧ UnaryHistory endpoint ∧ UnaryHistory sealRead ∧
              Cont readback endpoint sealRead ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier sealRoute sealPkg
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, _scaledEndpointUnary, _budgetUnary, readbackUnary,
    _sameRowsUnary, _routeUnary, _provenanceUnary, _namecertUnary, endpointUnary,
    _scalarWindow, _sourceWindow, _endpointsScaled, _scaledBudgetReadback,
    _readbackRouteProvenance, _provenanceNamecertEndpoint, _sameRowsAppend,
    endpointPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary endpointUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row endpoint ∨ hsame row sealRead)
          (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead
        ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sealPkg⟩
  }
  exact ⟨cert, readbackUnary, endpointUnary, sealUnary, sealRoute, endpointPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
