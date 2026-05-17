import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_cofinal_filter_handoff [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont window dyadic readback →
        Cont readback sealRow endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory readback ∧ UnaryHistory endpoint ∧ Cont muX muY meet ∧
                Cont meet window dyadic ∧ Cont window dyadic readback ∧
                  Cont readback sealRow endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowDyadicReadback readbackSealEndpoint endpointPkg
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, windowUnary, dyadicUnary,
    readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceMeet, meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary sealUnary readbackSealEndpoint
  exact
    ⟨meetUnary, windowUnary, dyadicUnary, readbackUnary, endpointUnary, sourceMeet,
      meetWindowDyadic, windowDyadicReadback, readbackSealEndpoint, endpointPkg⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
