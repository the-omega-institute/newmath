import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_unit_scalar_boundary [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint unitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      hsame scalar BHist.Empty →
        hsame scalarEndpoint sourceEndpoint →
          Cont sourceEndpoint budget unitRead →
            PkgSig bundle unitRead pkg →
              SemanticNameCert
                (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
                (fun _row : BHist =>
                  UnaryHistory sourceEndpoint ∧ UnaryHistory budget ∧
                    Cont sourceEndpoint budget unitRead)
                (fun _row : BHist => PkgSig bundle endpoint pkg ∧ PkgSig bundle unitRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _sameScalarEmpty sameScalarEndpointSource sourceEndpointBudget unitPkg
  obtain ⟨_scalarUnary, _sourceUnary, _windowUnary, scalarEndpointUnary,
    sourceEndpointUnary, _scaledEndpointUnary, budgetUnary, _readbackUnary, _sameRowsUnary,
    _routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary, _scalarWindow,
    _sourceWindow, _endpointsScaled, _scaledBudgetReadback, _readbackRouteProvenance,
    _provenanceNamecertEndpoint, _sameRowsAppend, endpointPkg⟩ := carrier
  have transportedSourceEndpoint : UnaryHistory sourceEndpoint :=
    unary_transport scalarEndpointUnary sameScalarEndpointSource
  have unitReadUnary : UnaryHistory unitRead :=
    unary_cont_closed transportedSourceEndpoint budgetUnary sourceEndpointBudget
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro unitRead ⟨hsame_refl unitRead, unitReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨sourceEndpointUnary, budgetUnary, sourceEndpointBudget⟩
    ledger_sound := by
      intro _row _source
      exact ⟨endpointPkg, unitPkg⟩
  }

end BEDC.Derived.RegularCauchyScaleUp
