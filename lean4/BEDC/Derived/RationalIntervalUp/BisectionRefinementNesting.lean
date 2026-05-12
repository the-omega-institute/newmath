import BEDC.Derived.RationalIntervalUp
import BEDC.Derived.RationalIntervalUp.Refinement

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_bisection_refinement_nesting [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint midpoint leftOrder
      leftTransport leftProvenance leftEndpoint rightOrder rightTransport rightProvenance
      rightEndpoint nestedConsumer nestedReadback nestedBridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory midpoint ->
        Cont left midpoint leftOrder ->
          Cont leftOrder containment leftTransport ->
            Cont leftTransport route leftProvenance ->
              Cont leftProvenance name leftEndpoint ->
                PkgSig bundle leftEndpoint pkg ->
                  Cont midpoint right rightOrder ->
                    Cont rightOrder containment rightTransport ->
                      Cont rightTransport route rightProvenance ->
                        Cont rightProvenance name rightEndpoint ->
                          PkgSig bundle rightEndpoint pkg ->
                            UnaryHistory nestedConsumer ->
                              Cont leftEndpoint nestedConsumer nestedReadback ->
                                Cont leftEndpoint nestedReadback nestedBridge ->
                                  PkgSig bundle nestedReadback pkg ->
                                    PkgSig bundle nestedBridge pkg ->
                                      RationalIntervalPacket left midpoint leftOrder containment
                                          leftTransport route leftProvenance name leftEndpoint
                                          bundle pkg ∧
                                        RationalIntervalPacket midpoint right rightOrder containment
                                            rightTransport route rightProvenance name rightEndpoint
                                            bundle pkg ∧
                                          UnaryHistory nestedReadback ∧
                                            UnaryHistory nestedBridge ∧
                                              Cont leftEndpoint nestedConsumer nestedReadback ∧
                                                Cont leftEndpoint nestedReadback nestedBridge ∧
                                                  PkgSig bundle nestedReadback pkg ∧
                                                    PkgSig bundle nestedBridge pkg := by
  intro packet midpointUnary leftOrderRow leftTransportRow leftProvenanceRow leftEndpointRow
    leftPkg rightOrderRow rightTransportRow rightProvenanceRow rightEndpointRow rightPkg
    nestedConsumerUnary nestedReadbackRow nestedBridgeRow nestedReadbackPkg nestedBridgePkg
  have bisection :=
    RationalIntervalPacket_midpoint_bisection_window packet midpointUnary leftOrderRow
      leftTransportRow leftProvenanceRow leftEndpointRow leftPkg rightOrderRow rightTransportRow
      rightProvenanceRow rightEndpointRow rightPkg
  have nesting :=
    RationalIntervalPacket_refinement_normal_form bisection.left nestedConsumerUnary
      nestedReadbackRow nestedBridgeRow nestedReadbackPkg nestedBridgePkg
  exact
    ⟨bisection.left, bisection.right, nesting.left, nesting.right.left,
      nesting.right.right.left, nesting.right.right.right.left,
      nesting.right.right.right.right.left, nesting.right.right.right.right.right⟩

end BEDC.Derived.RationalIntervalUp
