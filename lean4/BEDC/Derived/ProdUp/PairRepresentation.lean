import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ProdPairRep (Left Right : BHist → Prop) (h l r : BHist) : Prop :=
  Left l ∧ Right r ∧ Cont l r h

theorem ProdHistoryClassifier_fixed_pair_determinism
    {Left Right : BHist → Prop} {h k l r : BHist} :
    Left l → Right r → Cont l r h → Cont l r k →
      hsame h k ∧ ProdHistoryClassifier Left Right h k := by
  intro leftCarrier rightCarrier contH contK
  have sameHK : hsame h k := cont_deterministic contH contK
  constructor
  · exact sameHK
  · exact And.intro
      (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contH)
      (And.intro
        (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contK)
        sameHK)

theorem ProdPairRep_hsame_transport {Left Right : BHist → Prop} {h k l r : BHist} :
    ProdPairRep Left Right h l r → hsame h k → ProdPairRep Left Right k l r := by
  intro rep sameHK
  cases rep with
  | intro leftCarrier rest =>
      cases rest with
      | intro rightCarrier contH =>
          exact And.intro leftCarrier
            (And.intro rightCarrier (cont_result_hsame_transport contH sameHK))

end BEDC.Derived.ProdUp
