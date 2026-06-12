import BEDC.Derived.UnaryZeroSpineStandardIsoUp

namespace BEDC.Derived.UnaryZeroSpineStandardIsoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UnaryZeroSpineStandardIsoDownstreamUnblock [AskSetup] [PackageSetup]
    {unary axis length forward backward transport routes provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport routes provenance
        cert bundle pkg →
      Cont routes cert endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory unary ∧ UnaryHistory axis ∧ UnaryHistory length ∧
            UnaryHistory forward ∧ UnaryHistory backward ∧ UnaryHistory routes ∧
              UnaryHistory endpoint ∧ Cont unary length forward ∧
                Cont axis length backward ∧ Cont forward backward routes ∧
                  Cont routes cert endpoint ∧ PkgSig bundle routes pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier routesCert endpointPkg
  obtain ⟨unaryRow, axisRow, lengthRow, _provenanceUnary, certUnary, forwardRoute,
    backwardRoute, routesRoute, _provenanceRoute, _transportRoute, routesPkg⟩ := carrier
  have forwardUnary : UnaryHistory forward :=
    unary_cont_closed unaryRow lengthRow forwardRoute
  have backwardUnary : UnaryHistory backward :=
    unary_cont_closed axisRow lengthRow backwardRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed forwardUnary backwardUnary routesRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routesUnary certUnary routesCert
  exact
    ⟨unaryRow, axisRow, lengthRow, forwardUnary, backwardUnary, routesUnary,
      endpointUnary, forwardRoute, backwardRoute, routesRoute, routesCert, routesPkg,
      endpointPkg⟩

end BEDC.Derived.UnaryZeroSpineStandardIsoUp
