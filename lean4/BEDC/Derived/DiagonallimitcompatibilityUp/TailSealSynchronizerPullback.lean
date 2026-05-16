import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTailSealSynchronizerPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request tail selector sync locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory request →
        UnaryHistory tail →
          Cont sealRow request selector →
            Cont selector tail sync →
              Cont sync readback locked →
                Cont locked realSeal endpoint →
                  PkgSig bundle endpoint pkg →
                    UnaryHistory selector ∧ UnaryHistory sync ∧ UnaryHistory locked ∧
                      UnaryHistory endpoint ∧ Cont sealRow request selector ∧
                        Cont selector tail sync ∧ Cont sync readback locked ∧
                          Cont locked realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier requestUnary tailUnary sealRowRequestSelector selectorTailSync
    syncReadbackLocked lockedRealSealEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed sealRowUnary requestUnary sealRowRequestSelector
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed selectorUnary tailUnary selectorTailSync
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed syncUnary readbackUnary syncReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨selectorUnary, syncUnary, lockedUnary, endpointUnary, sealRowRequestSelector,
      selectorTailSync, syncReadbackLocked, lockedRealSealEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
