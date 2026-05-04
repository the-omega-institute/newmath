import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_hsame_bordered_e1_singleton_payload_readback
    {pref pref' suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist}
    {x y : BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame pref pref' ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame suffix suffix' ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          ((pref ++ [BEDC.FKernel.Hist.BHist.e1 x]) ++ suffix)
          ((pref' ++ [BEDC.FKernel.Hist.BHist.e1 y]) ++ suffix') ->
          BEDC.FKernel.Hist.hsame x y := by
  intro prefixSame suffixSame framedSame
  have withoutSuffix :
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        (pref ++ [BEDC.FKernel.Hist.BHist.e1 x])
        (pref' ++ [BEDC.FKernel.Hist.BHist.e1 y]) :=
    ListClassifierSpec_append_right_cancel_with_hsame_suffix suffixSame framedSame
  have singletonSame :
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        [BEDC.FKernel.Hist.BHist.e1 x] [BEDC.FKernel.Hist.BHist.e1 y] :=
    ListClassifierSpec_hsame_append_left_cancel_classified prefixSame withoutSuffix
  exact BEDC.FKernel.Hist.hsame_e1_iff.mp
    (ListClassifierSpec_hsame_singleton_iff.mp singletonSame)

end BEDC.Derived.ListUp
