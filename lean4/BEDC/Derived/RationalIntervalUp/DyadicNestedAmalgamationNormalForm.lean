import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_dyadic_nested_amalgamation_normal_form
    [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint nested overlap
      amalgam : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory nested ->
        Cont endpoint nested overlap ->
          Cont overlap containment amalgam ->
            PkgSig bundle amalgam pkg ->
              UnaryHistory endpoint ∧ UnaryHistory nested ∧ UnaryHistory overlap ∧
                UnaryHistory amalgam ∧ Cont endpoint nested overlap ∧
                  Cont overlap containment amalgam ∧ PkgSig bundle amalgam pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet nestedUnary endpointNestedOverlap overlapContainmentAmalgam amalgamPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, containmentUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder,
    _orderContainmentTransport, _transportRouteProvenance, _provenanceNameEndpoint,
    _endpointPkg⟩ := packet
  have overlapUnary : UnaryHistory overlap :=
    unary_cont_closed endpointUnary nestedUnary endpointNestedOverlap
  have amalgamUnary : UnaryHistory amalgam :=
    unary_cont_closed overlapUnary containmentUnary overlapContainmentAmalgam
  exact
    ⟨endpointUnary, nestedUnary, overlapUnary, amalgamUnary, endpointNestedOverlap,
      overlapContainmentAmalgam, amalgamPkg⟩

end BEDC.Derived.RationalIntervalUp
