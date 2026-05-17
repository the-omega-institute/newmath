import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_consumer_threshold [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont sealRow readback sealRead →
        Cont sealRead realSeal terminal →
          PkgSig bundle terminal pkg →
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                UnaryHistory sealRead ∧ UnaryHistory terminal ∧
                  Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                    Cont sealRow readback sealRead ∧ Cont sealRead realSeal terminal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier sealRowReadbackSealRead sealReadRealSealTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSealRow, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sealRowUnary readbackUnary sealRowReadbackSealRead
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary realSealUnary sealReadRealSealTerminal
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, sealReadUnary, terminalUnary, diagonalTriangleSealRow,
      dyadicWindowsReadback, sealRowReadbackSealRead, sealReadRealSealTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
