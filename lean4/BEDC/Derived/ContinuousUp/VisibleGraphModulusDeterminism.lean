import BEDC.Derived.ContinuousUp.GraphModulusReadback
import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_modulus_context_graph_modulus_deterministic
    {p q source map map' target modulus modulus' cert : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
      ContinuousFunctionCarrier (append p source) map' (append p target) (append modulus' q)
        (append (append p cert) q) ->
        hsame map map' ∧ hsame modulus modulus' := by
  intro left right
  have leftCarrier :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp left
  have rightCarrier :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map') (target := target) (modulus := modulus')
      (cert := cert)).mp right
  have leftReadback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback leftCarrier.right.right
  have rightReadback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback rightCarrier.right.right
  exact And.intro
    (cont_left_cancel leftReadback.left rightReadback.left)
    (cont_left_cancel leftReadback.right.left rightReadback.right.left)

end BEDC.Derived.ContinuousUp
