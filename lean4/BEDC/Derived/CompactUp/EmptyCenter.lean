import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_empty_center_nonempty_precision_shape_iff {net precision : BHist} :
    (CompactNetWitness BHist.Empty precision net /\ (hsame precision BHist.Empty -> False)) <->
      exists r : BHist, net = BHist.e1 r /\ precision = BHist.e1 r /\ UnaryHistory r := by
  constructor
  · intro data
    have sameNetPrecision : hsame net precision :=
      cont_left_unit_result data.left.right.right.right
    cases precision with
    | Empty =>
        exact False.elim (data.right (hsame_refl BHist.Empty))
    | e0 t =>
        exact False.elim (unary_no_zero_extension data.left.right.left)
    | e1 r =>
        cases sameNetPrecision
        exact Exists.intro r
          (And.intro rfl (And.intro rfl (unary_e1_inversion data.left.right.left)))
  · intro witness
    cases witness with
    | intro r data =>
        cases data with
        | intro netEq rest =>
            cases rest with
            | intro precisionEq tailCarrier =>
                cases netEq
                cases precisionEq
                constructor
                · exact And.intro unary_empty
                    (And.intro (unary_e1_closed tailCarrier)
                      (And.intro (unary_e1_closed tailCarrier)
                        (cont_left_unit (BHist.e1 r))))
                · intro sameEmpty
                  exact not_hsame_e1_empty sameEmpty

end BEDC.Derived.CompactUp
