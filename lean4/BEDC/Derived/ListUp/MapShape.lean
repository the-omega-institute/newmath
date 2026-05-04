import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem ListClassifierSpec_hsame_map_e1_left_shape :
    forall {xs ys : ListCarrier BHist},
      ListClassifierSpec hsame (xs.map BHist.e1) ys ->
        exists zs : ListCarrier BHist,
          ys = zs.map BHist.e1 ∧ ListClassifierSpec hsame xs zs := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          exact Exists.intro [] (And.intro rfl (by constructor))
      | cons _ _ =>
          cases classified
  | cons x xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons y ys =>
          cases classified with
          | intro headSame tailSame =>
              have headShape := hsame_e1_inversion headSame
              cases headShape with
              | intro z headData =>
                  cases headData with
                  | intro yEq tailHeadSame =>
                      have tailShape := ih tailSame
                      cases tailShape with
                      | intro zs tailData =>
                          cases tailData with
                          | intro ysEq tailClassified =>
                              exists z :: zs
                              constructor
                              · cases yEq
                                cases ysEq
                                rfl
                              · constructor
                                · exact tailHeadSame
                                · exact tailClassified

theorem ListClassifierSpec_hsame_map_e1_map_e0_empty :
    forall {xs ys : ListCarrier BHist},
      ListClassifierSpec hsame (xs.map BHist.e1) (ys.map BHist.e0) ->
        xs = [] /\ ys = [] := by
  intro xs
  cases xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          constructor
          · rfl
          · rfl
      | cons _ _ =>
          cases classified
  | cons _ _ =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons _ _ =>
          cases classified with
          | intro headSame _ =>
              exact False.elim (not_hsame_e1_e0 headSame)

end BEDC.Derived.ListUp
