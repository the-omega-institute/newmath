import BEDC.Derived.ListUp.FramedEndpoint

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

theorem ListClassifierSpec_hsame_bordered_e0_singleton_payload_readback
    {pref pref' suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist}
    {x y : BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame pref pref' ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame suffix suffix' ->
        ListClassifierSpec BEDC.FKernel.Hist.hsame
          ((pref ++ [BEDC.FKernel.Hist.BHist.e0 x]) ++ suffix)
          ((pref' ++ [BEDC.FKernel.Hist.BHist.e0 y]) ++ suffix') ->
          BEDC.FKernel.Hist.hsame x y := by
  intro prefixSame suffixSame framedSame
  have withoutSuffix :
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        (pref ++ [BEDC.FKernel.Hist.BHist.e0 x])
        (pref' ++ [BEDC.FKernel.Hist.BHist.e0 y]) :=
    ListClassifierSpec_append_right_cancel_with_hsame_suffix suffixSame framedSame
  have singletonSame :
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        [BEDC.FKernel.Hist.BHist.e0 x] [BEDC.FKernel.Hist.BHist.e0 y] :=
    ListClassifierSpec_hsame_append_left_cancel_classified prefixSame withoutSuffix
  exact BEDC.FKernel.Hist.hsame_e0_iff.mp
    (ListClassifierSpec_hsame_singleton_iff.mp singletonSame)

theorem FramedListBridgeClassifier_bordered_singleton_payload_readback
    {A : BEDC.FKernel.Hist.BHist -> Prop}
    (cert : BEDC.FKernel.NameCert.NameCert A BEDC.FKernel.Hist.hsame)
    (compat : ListSourceHsameCompatible A BEDC.FKernel.Hist.hsame)
    {pref pref' suffix suffix' : ListCarrier BEDC.FKernel.Hist.BHist}
    {x y h k : BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.FKernel.Hist.hsame pref pref' ->
      ListClassifierSpec BEDC.FKernel.Hist.hsame suffix suffix' ->
        FramedListSpineRep A h ((pref ++ [x]) ++ suffix) ->
          FramedListSpineRep A k ((pref' ++ [y]) ++ suffix') ->
            FramedListBridgeClassifier A BEDC.FKernel.Hist.hsame h k ->
              BEDC.FKernel.Hist.hsame x y := by
  intro prefixSame suffixSame leftRep rightRep bridge
  have framedSame :
      ListClassifierSpec BEDC.FKernel.Hist.hsame
        ((pref ++ [x]) ++ suffix) ((pref' ++ [y]) ++ suffix') :=
    (FramedListBridgeClassifier_displayed_spine_exactness cert compat leftRep rightRep).mp
      bridge
  have withoutSuffix :
      ListClassifierSpec BEDC.FKernel.Hist.hsame (pref ++ [x]) (pref' ++ [y]) :=
    ListClassifierSpec_append_right_cancel_with_hsame_suffix suffixSame framedSame
  have singletonSame : ListClassifierSpec BEDC.FKernel.Hist.hsame [x] [y] :=
    ListClassifierSpec_hsame_append_left_cancel_classified prefixSame withoutSuffix
  exact ListClassifierSpec_hsame_singleton_iff.mp singletonSame

end BEDC.Derived.ListUp
