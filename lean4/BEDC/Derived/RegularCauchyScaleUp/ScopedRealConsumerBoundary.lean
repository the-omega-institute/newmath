import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_scoped_real_consumer_boundary [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg ->
      hsame realRead readback ->
        UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
          UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
            UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
              UnaryHistory realRead ∧ Cont scalar window scalarEndpoint ∧
                Cont source window sourceEndpoint ∧
                  Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                    Cont scaledEndpoint budget readback ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameRealRead
  obtain ⟨scalarUnary, sourceUnary, windowUnary, scalarEndpointUnary, sourceEndpointUnary,
    scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary, _routeUnary,
    _provenanceUnary, _namecertUnary, _endpointUnary, scalarWindow, sourceWindow,
    endpointsScaled, scaledBudgetReadback, _readbackRoute, _provenanceNamecert,
    _sameRowsAppend, endpointPkg⟩ := carrier
  exact
    ⟨scalarUnary, sourceUnary, windowUnary, scalarEndpointUnary, sourceEndpointUnary,
      scaledEndpointUnary, budgetUnary, readbackUnary,
      unary_transport readbackUnary (hsame_symm sameRealRead), scalarWindow, sourceWindow,
      endpointsScaled, scaledBudgetReadback, endpointPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
