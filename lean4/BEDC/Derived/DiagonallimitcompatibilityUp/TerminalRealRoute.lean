import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTerminalRealRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal terminal →
        PkgSig bundle terminal pkg →
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory terminal ∧
                  Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                    Cont readback realSeal terminal ∧ Cont route cert transport ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier readbackRealSealTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, terminalUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealTerminal,
      routeCertTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
