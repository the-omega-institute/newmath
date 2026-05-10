import BEDC.Derived.ChernWeilUp

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ChernWeilCarrierEnvelope_standard_bridge_boundary
    {curvature derham polynomial connectionLedger characteristic provenance endpoint
      representative classRow bridge : BHist} :
    ChernWeilCarrierEnvelope curvature derham polynomial connectionLedger characteristic provenance
        endpoint ->
      UnaryHistory representative ->
        Cont endpoint representative classRow ->
          Cont classRow connectionLedger bridge ->
            UnaryHistory classRow ∧ UnaryHistory bridge ∧
              hsame classRow (append endpoint representative) ∧
                hsame bridge (append classRow connectionLedger) ∧
                  hsame endpoint (append provenance connectionLedger) := by
  intro envelope representativeUnary classRowCont bridgeCont
  have characteristicUnary : UnaryHistory characteristic :=
    unary_cont_closed envelope.left envelope.right.right.left
      envelope.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed characteristicUnary envelope.right.left
      envelope.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary envelope.right.right.right.left
      envelope.right.right.right.right.right.right
  have classRowUnary : UnaryHistory classRow :=
    unary_cont_closed endpointUnary representativeUnary classRowCont
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed classRowUnary envelope.right.right.right.left bridgeCont
  exact And.intro classRowUnary
    (And.intro bridgeUnary
      (And.intro classRowCont
        (And.intro bridgeCont envelope.right.right.right.right.right.right)))

end BEDC.Derived.ChernWeilUp
