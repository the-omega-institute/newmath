import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_tailmeet_refinement_seal_route [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailMeet refinement agreement endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal tailMeet →
        Cont tailMeet route refinement →
          Cont refinement realSeal agreement →
            Cont agreement cert endpoint →
              PkgSig bundle endpoint pkg →
                UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                  UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                    UnaryHistory tailMeet ∧ UnaryHistory refinement ∧
                      UnaryHistory agreement ∧ UnaryHistory endpoint ∧
                        Cont readback realSeal tailMeet ∧ Cont tailMeet route refinement ∧
                          Cont refinement realSeal agreement ∧ Cont agreement cert endpoint ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier readbackRealTail tailMeetRouteRefinement refinementRealAgreement
    agreementCertEndpoint endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed readbackUnary realSealUnary readbackRealTail
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed tailMeetUnary routeUnary tailMeetRouteRefinement
  have agreementUnary : UnaryHistory agreement :=
    unary_cont_closed refinementUnary realSealUnary refinementRealAgreement
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed agreementUnary certUnary agreementCertEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      tailMeetUnary, refinementUnary, agreementUnary, endpointUnary, readbackRealTail,
      tailMeetRouteRefinement, refinementRealAgreement, agreementCertEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
