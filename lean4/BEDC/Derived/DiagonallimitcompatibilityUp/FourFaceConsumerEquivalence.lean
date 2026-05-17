import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityFourFaceConsumerEquivalence [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      cauchyRoute uniformRoute consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont windows dyadic cauchyRoute →
        Cont dyadic readback uniformRoute →
          Cont cauchyRoute uniformRoute consumer →
            PkgSig bundle consumer pkg →
              UnaryHistory cauchyRoute ∧ UnaryHistory uniformRoute ∧
                UnaryHistory consumer ∧ Cont windows dyadic cauchyRoute ∧
                  Cont dyadic readback uniformRoute ∧
                    Cont cauchyRoute uniformRoute consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier windowsDyadicCauchy dyadicReadbackUniform cauchyUniformConsumer consumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRoute :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicCauchy
  have uniformUnary : UnaryHistory uniformRoute :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackUniform
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed cauchyUnary uniformUnary cauchyUniformConsumer
  exact
    ⟨cauchyUnary, uniformUnary, consumerUnary, windowsDyadicCauchy,
      dyadicReadbackUniform, cauchyUniformConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
