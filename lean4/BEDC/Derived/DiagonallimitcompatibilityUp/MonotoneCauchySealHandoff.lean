import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityMonotoneCauchySealHandoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      monotoneBase monotoneStep monotoneWindow handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory monotoneBase →
        UnaryHistory monotoneStep →
          hsame monotoneWindow windows →
            Cont monotoneBase monotoneStep monotoneWindow →
              Cont monotoneWindow readback handoff →
                Cont handoff realSeal sealRead →
                  PkgSig bundle sealRead pkg →
                    UnaryHistory monotoneWindow ∧ UnaryHistory handoff ∧
                      UnaryHistory sealRead ∧ hsame monotoneWindow windows ∧
                        Cont monotoneWindow readback handoff ∧
                          Cont handoff realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier monotoneBaseUnary monotoneStepUnary monotoneWindowSameWindows
    monotoneBaseStepWindow monotoneWindowReadbackHandoff handoffRealSealRead sealReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have monotoneWindowUnary : UnaryHistory monotoneWindow :=
    unary_transport_symm windowsUnary monotoneWindowSameWindows
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed monotoneWindowUnary readbackUnary monotoneWindowReadbackHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary realSealUnary handoffRealSealRead
  exact
    ⟨monotoneWindowUnary, handoffUnary, sealReadUnary, monotoneWindowSameWindows,
      monotoneWindowReadbackHandoff, handoffRealSealRead, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
