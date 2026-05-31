import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_scoped_closure_route [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      Cont endpoint readback realSeal ->
        PkgSig bundle realSeal pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row scalar ∨ hsame row source ∨ hsame row window ∨
                  hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback ∨
                    hsame row endpoint ∨ hsame row realSeal)
              (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
              UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ Cont scalar window scalarEndpoint ∧
                  Cont source window sourceEndpoint ∧
                    Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                      Cont scaledEndpoint budget readback ∧
                        Cont endpoint readback realSeal ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointReadbackRealSeal realSealPkg
  obtain ⟨scalarUnary, sourceUnary, windowUnary, _scalarEndpointUnary,
    _sourceEndpointUnary, scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, endpointUnary, scalarWindow,
    sourceWindow, endpointsScaled, scaledBudgetReadback, _readbackRouteProvenance,
    _provenanceNamecertEndpoint, _sameRowsAppend, endpointPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackRealSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scalar ∨ hsame row source ∨ hsame row window ∨
              hsame row scaledEndpoint ∨ hsame row budget ∨ hsame row readback ∨
                hsame row endpoint ∨ hsame row realSeal)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal
        ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, realSealPkg⟩
  }
  exact
    ⟨cert, scalarUnary, sourceUnary, windowUnary, scaledEndpointUnary, budgetUnary,
      readbackUnary, realSealUnary, scalarWindow, sourceWindow, endpointsScaled,
      scaledBudgetReadback, endpointReadbackRealSeal, endpointPkg, realSealPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
