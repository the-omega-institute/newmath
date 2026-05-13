import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitCompatibilityCarrier [AskSetup] [PackageSetup]
    (diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
          Cont readback realSeal route ∧ Cont route cert transport ∧
            PkgSig bundle provenance pkg

theorem DiagonalLimitCompatibilityNonEscape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
                Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, endpointUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
