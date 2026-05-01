import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

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
