import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_budget_public_route_cover [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailMeet refinement agreement endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic tailMeet ->
        Cont tailMeet windows refinement ->
          Cont refinement readback agreement ->
            Cont agreement realSeal endpoint ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory tailMeet ∧ UnaryHistory refinement ∧ UnaryHistory agreement ∧
                  UnaryHistory endpoint ∧ Cont diagonal dyadic tailMeet ∧
                    Cont tailMeet windows refinement ∧ Cont refinement readback agreement ∧
                      Cont agreement realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier diagonalDyadicTailMeet tailMeetWindowsRefinement
    refinementReadbackAgreement agreementRealSealEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicTailMeet
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed tailMeetUnary windowsUnary tailMeetWindowsRefinement
  have agreementUnary : UnaryHistory agreement :=
    unary_cont_closed refinementUnary readbackUnary refinementReadbackAgreement
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed agreementUnary realSealUnary agreementRealSealEndpoint
  exact
    ⟨tailMeetUnary, refinementUnary, agreementUnary, endpointUnary, diagonalDyadicTailMeet,
      tailMeetWindowsRefinement, refinementReadbackAgreement, agreementRealSealEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
