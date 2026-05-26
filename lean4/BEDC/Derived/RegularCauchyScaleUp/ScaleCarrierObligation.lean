import BEDC.Derived.RegularCauchyScaleUp

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScaleCarrier_scale_carrier_obligation [AskSetup] [PackageSetup]
    {scalar source window scalarEndpoint sourceEndpoint scaledEndpoint budget readback sameRows
      route provenance namecert endpoint admissionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScaleCarrier scalar source window scalarEndpoint sourceEndpoint scaledEndpoint
        budget readback sameRows route provenance namecert endpoint bundle pkg →
      Cont scalar source admissionRead →
        PkgSig bundle admissionRead pkg →
          UnaryHistory scalar ∧ UnaryHistory source ∧ UnaryHistory window ∧
            UnaryHistory scalarEndpoint ∧ UnaryHistory sourceEndpoint ∧
              UnaryHistory scaledEndpoint ∧ UnaryHistory budget ∧ UnaryHistory readback ∧
                UnaryHistory admissionRead ∧ Cont scalar window scalarEndpoint ∧
                  Cont source window sourceEndpoint ∧
                    Cont scalarEndpoint sourceEndpoint scaledEndpoint ∧
                      Cont scalar source admissionRead ∧ hsame sameRows (append scalar source) ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle admissionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier scalarSource admissionPkg
  obtain ⟨scalarUnary, sourceUnary, windowUnary, scalarEndpointUnary, sourceEndpointUnary,
    scaledEndpointUnary, budgetUnary, readbackUnary, _sameRowsUnary, _routeUnary,
    _provenanceUnary, _namecertUnary, _endpointUnary, scalarWindow, sourceWindow,
    endpointsScaled, _scaledBudgetReadback, _readbackRouteProvenance,
    _provenanceNamecertEndpoint, sameRowsAppend, endpointPkg⟩ := carrier
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed scalarUnary sourceUnary scalarSource
  exact
    ⟨scalarUnary,
      sourceUnary,
      windowUnary,
      scalarEndpointUnary,
      sourceEndpointUnary,
      scaledEndpointUnary,
      budgetUnary,
      readbackUnary,
      admissionUnary,
      scalarWindow,
      sourceWindow,
      endpointsScaled,
      scalarSource,
      sameRowsAppend,
      endpointPkg,
      admissionPkg⟩

end BEDC.Derived.RegularCauchyScaleUp
