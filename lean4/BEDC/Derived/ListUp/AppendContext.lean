import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_BHist_append_left_cancel_classified
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    {pref pref' xs ys : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec sameA pref pref' ->
      ListClassifierSpec sameA (pref ++ xs) (pref' ++ ys) ->
        ListClassifierSpec sameA xs ys := by
  intro prefixClass appendClass
  induction pref generalizing pref' with
  | nil =>
      cases pref' with
      | nil =>
          exact appendClass
      | cons _ _ =>
          cases prefixClass
  | cons _ pref ih =>
      cases pref' with
      | nil =>
          cases prefixClass
      | cons _ pref' =>
          exact ih prefixClass.right appendClass.right

theorem ListClassifierSpec_hsame_append_context_iff
    {pref pref' xs ys suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame pref pref' →
      ListClassifierSpec BEDC.FKernel.Hist.hsame suffix suffix' →
        (ListClassifierSpec BEDC.FKernel.Hist.hsame
          (pref ++ (xs ++ suffix)) (pref' ++ (ys ++ suffix')) ↔
            ListClassifierSpec BEDC.FKernel.Hist.hsame xs ys) := by
  intro prefixClass suffixClass
  constructor
  · intro contextClass
    have coreWithSuffix :
        ListClassifierSpec BEDC.FKernel.Hist.hsame (xs ++ suffix) (ys ++ suffix') :=
      ListClassifierSpec_hsame_append_left_cancel_classified prefixClass contextClass
    exact ListClassifierSpec_append_right_cancel_with_hsame_suffix suffixClass coreWithSuffix
  · intro coreClass
    exact ListClassifierSpec_append_hsame prefixClass
      (ListClassifierSpec_append_hsame coreClass suffixClass)

end BEDC.Derived.ListUp
