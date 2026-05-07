import BEDC.Derived.NatTransUp.EmptyComponentPrefix
import BEDC.Derived.NatTransUp.EmptyVertComp
import BEDC.Derived.NatTransUp.VertCycleEmptyComponents

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem NatTransPrefixNaturalIso_component_cycle_empty_boundary
    {p q a eta epsilon etaepsilon epsiloneta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q p a epsilon -> Cont eta epsilon etaepsilon ->
        Cont epsilon eta epsiloneta -> hsame etaepsilon BHist.Empty ->
          hsame epsiloneta BHist.Empty ->
            NatTransPrefixComponentCarrier p q a BHist.Empty ∧
              NatTransPrefixComponentCarrier q p a BHist.Empty ∧ hsame eta BHist.Empty ∧
                hsame epsilon BHist.Empty ∧ hsame p q := by
  intro etaCarrier epsilonCarrier etaEpsilonCont epsilonEtaCont etaEpsilonEmpty
    epsilonEtaEmpty
  have cycleEmpty :
      NatTransPrefixComponentCarrier p q a BHist.Empty ∧
        NatTransPrefixComponentCarrier q p a BHist.Empty ∧ hsame p q :=
    NatTransPrefixComponentCarrier_vert_cycle_empty_components etaCarrier epsilonCarrier
  have forwardData :
      hsame eta BHist.Empty ∧ hsame epsilon BHist.Empty ∧ hsame p q ∧ hsame q p :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff etaCarrier epsilonCarrier
      etaEpsilonCont).mp etaEpsilonEmpty
  have reverseData :
      hsame epsilon BHist.Empty ∧ hsame eta BHist.Empty ∧ hsame q p ∧ hsame p q :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff epsilonCarrier etaCarrier
      epsilonEtaCont).mp epsilonEtaEmpty
  have samePrefix : hsame p q :=
    (NatTransPrefixComponentCarrier_component_empty_prefix_iff etaCarrier).mp
      forwardData.left
  exact And.intro cycleEmpty.left
    (And.intro cycleEmpty.right.left
      (And.intro reverseData.right.left
        (And.intro reverseData.left samePrefix)))

end BEDC.Derived.NatTransUp
