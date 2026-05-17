import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySharedTailBudgetFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      fusionThreshold agreementSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows dyadic fusionThreshold ->
        Cont fusionThreshold readback agreementSeal ->
          PkgSig bundle agreementSeal pkg ->
            UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory fusionThreshold ∧
              UnaryHistory readback ∧ UnaryHistory agreementSeal ∧
                Cont windows dyadic fusionThreshold ∧
                  Cont fusionThreshold readback agreementSeal ∧
                    Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle agreementSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowsDyadicFusion fusionReadbackAgreement agreementPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have fusionUnary : UnaryHistory fusionThreshold :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicFusion
  have agreementUnary : UnaryHistory agreementSeal :=
    unary_cont_closed fusionUnary readbackUnary fusionReadbackAgreement
  exact
    ⟨windowsUnary, dyadicUnary, fusionUnary, readbackUnary, agreementUnary,
      windowsDyadicFusion, fusionReadbackAgreement, readbackRealSealRoute, provenancePkg,
      agreementPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
