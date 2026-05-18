import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_finite_consumer_completeness [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint consumer readback window
      final : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg →
      UnaryHistory consumer →
        Cont endpoint consumer readback →
          Cont readback transport window →
            Cont window route final →
              PkgSig bundle final pkg →
                UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory order ∧
                  UnaryHistory containment ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                    UnaryHistory endpoint ∧ UnaryHistory readback ∧ UnaryHistory window ∧
                      UnaryHistory final ∧ Cont left right order ∧
                        Cont order containment transport ∧ Cont endpoint consumer readback ∧
                          Cont readback transport window ∧ Cont window route final ∧
                            PkgSig bundle endpoint pkg ∧ PkgSig bundle final pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet consumerUnary endpointConsumerReadback readbackTransportWindow windowRouteFinal
    finalPkg
  rcases packet with
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, transportUnary, routeUnary,
      _provenanceUnary, _nameUnary, endpointUnary, leftRightOrder, orderContainmentTransport,
      _transportRouteProvenance, _provenanceNameEndpoint, endpointPkg⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary endpointConsumerReadback
  have windowUnary : UnaryHistory window :=
    unary_cont_closed readbackUnary transportUnary readbackTransportWindow
  have finalUnary : UnaryHistory final :=
    unary_cont_closed windowUnary routeUnary windowRouteFinal
  exact
    ⟨leftUnary, rightUnary, orderUnary, containmentUnary, transportUnary, routeUnary,
      endpointUnary, readbackUnary, windowUnary, finalUnary, leftRightOrder,
      orderContainmentTransport, endpointConsumerReadback, readbackTransportWindow,
      windowRouteFinal, endpointPkg, finalPkg⟩

end BEDC.Derived.RationalIntervalUp
