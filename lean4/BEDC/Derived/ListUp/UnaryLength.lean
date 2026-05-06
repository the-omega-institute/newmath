import BEDC.Derived.ListUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ListUnaryLength : ListCarrier BHist -> BHist
  | [] => BHist.Empty
  | _ :: xs => BHist.e1 (ListUnaryLength xs)

theorem ListUnaryLength_append_cont {xs ys : ListCarrier BHist} :
    Cont (ListUnaryLength ys) (ListUnaryLength xs) (ListUnaryLength (xs ++ ys)) := by
  induction xs with
  | nil =>
      exact cont_right_unit (ListUnaryLength ys)
  | cons _ xs ih =>
      exact cont_step_one ih

theorem ListClassifierSpec_unary_length_token_hsame :
    forall {xs ys : ListCarrier BHist},
      ListClassifierSpec hsame xs ys -> hsame (ListUnaryLength xs) (ListUnaryLength ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          exact hsame_refl BHist.Empty
      | cons y ys =>
          cases classified
  | cons x xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons y ys =>
          cases classified with
          | intro sameHead sameTail =>
              exact hsame_e1_congr (ih sameTail)

end BEDC.Derived.ListUp
