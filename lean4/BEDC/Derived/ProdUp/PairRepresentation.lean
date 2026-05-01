import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ProdPairRep (Left Right : BHist → Prop) (h l r : BHist) : Prop :=
  Left l ∧ Right r ∧ Cont l r h

def ProdPairRepCoherent (Left Right : BHist → Prop)
    (LeftEq RightEq : BHist → BHist → Prop) : Prop :=
  ∀ {h l r l' r' : BHist},
    ProdPairRep Left Right h l r →
      ProdPairRep Left Right h l' r' →
        LeftEq l l' ∧ RightEq r r'

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

theorem ProdPairRep_fixed_endpoint_exactness {Left Right : BHist → Prop} {h k l r : BHist} :
    ProdPairRep Left Right h l r → (ProdPairRep Left Right k l r ↔ hsame h k) := by
  intro repH
  constructor
  · intro repK
    cases repH with
    | intro leftCarrier restH =>
        cases restH with
        | intro rightCarrier contH =>
            cases repK with
            | intro _leftCarrierK restK =>
                cases restK with
                | intro _rightCarrierK contK =>
                    exact
                      (ProdHistoryClassifier_fixed_pair_determinism
                        leftCarrier rightCarrier contH contK).left
  · intro sameHK
    exact ProdPairRep_hsame_transport repH sameHK

theorem ProdPairRep_hsame_coherence {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k l r l' r' : BHist} :
    ProdPairRepCoherent Left Right LeftEq RightEq →
      ProdPairRep Left Right h l r →
        ProdPairRep Left Right k l' r' →
          hsame h k → LeftEq l l' ∧ RightEq r r' := by
  intro coherent repH repK sameHK
  have repKAtH : ProdPairRep Left Right h l' r' :=
    ProdPairRep_hsame_transport repK (hsame_symm sameHK)
  exact coherent repH repKAtH

theorem ProdHistoryClassifier_cont_congr {Left Right : BHist → Prop}
    (left_transport : ∀ {x y : BHist}, hsame x y → Left x → Left y)
    (right_transport : ∀ {x y : BHist}, hsame x y → Right x → Right y)
    {l l' r r' h h' : BHist} :
    Left l → Right r → hsame l l' → hsame r r' → Cont l r h → Cont l' r' h' →
      ProdHistoryClassifier Left Right h h' := by
  intro leftCarrier rightCarrier sameLeft sameRight contH contH'
  have leftCarrier' : Left l' := left_transport sameLeft leftCarrier
  have rightCarrier' : Right r' := right_transport sameRight rightCarrier
  have sameEndpoints : hsame h h' :=
    cont_respects_hsame sameLeft sameRight contH contH'
  exact And.intro
    (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contH)
    (And.intro
      (ProdHistoryCarrier_cont_intro leftCarrier' rightCarrier' contH')
      sameEndpoints)

end BEDC.Derived.ProdUp
