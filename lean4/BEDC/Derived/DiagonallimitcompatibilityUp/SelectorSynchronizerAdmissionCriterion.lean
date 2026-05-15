import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_selector_synchronizer_admission_criterion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert selector synchronizer endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows selector ->
        Cont selector readback synchronizer ->
          Cont synchronizer realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory synchronizer ∧
                  UnaryHistory endpoint ∧ Cont dyadic windows selector ∧
                    Cont selector readback synchronizer ∧
                      Cont synchronizer realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsSelector selectorReadbackSynchronizer
    synchronizerRealSealEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsSelector
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackSynchronizer
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed synchronizerUnary realSealUnary synchronizerRealSealEndpoint
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, selectorUnary,
      synchronizerUnary, endpointUnary, dyadicWindowsSelector, selectorReadbackSynchronizer,
      synchronizerRealSealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
