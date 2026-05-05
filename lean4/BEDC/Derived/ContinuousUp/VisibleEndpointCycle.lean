import BEDC.Derived.ContinuousUp.EndpointCycle
import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_modulus_context_cycle_tails_empty
    {p q source map target modulus cert : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
      hsame source cert -> hsame map BHist.Empty ∧ hsame modulus BHist.Empty := by
  intro visible sameEndpoint
  have central :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp visible
  exact ContinuousFunctionCarrier_endpoint_cert_cycle_tails_empty central.right.right sameEndpoint

end BEDC.Derived.ContinuousUp
