import BEDC.MetaCIC.HostBridge
import BEDC.MetaCIC.TypingV2

namespace BEDC.MetaCIC.HostBridgeDemos

open BEDC.MetaCIC
open BEDC.MetaCIC.HostBridge

#reflect_metacic (Term.lam Term.sort (Term.var 0))

#metacic_decide (Term.sort)

#metacic_decide (Term.pi Term.sort Term.sort)

#metacic_decide (Term.lam Term.sort (Term.var 0))

#metacic_decide (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)

#metacic_decide (Term.pi (Term.var 0) (Term.var 1))

example : infer [] (Term.lam Term.sort (Term.var 0)) =
    some (Term.pi Term.sort Term.sort) := rfl

example : V2.HasTypeV2 [] (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort) := by
  exact V2.id_sort_well_typed_V2

example : infer [] (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) =
    some Term.sort := rfl

example : V2.HasTypeV2 []
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort := by
  exact V2.id_sort_applied_V2

example : V2.HasTypeV2 [Term.sort] (Term.pi (Term.var 0) (Term.var 1))
    Term.sort := by
  exact V2.pi_dependent_identity_type_V2

end BEDC.MetaCIC.HostBridgeDemos
