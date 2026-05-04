import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem ratup_fieldup_rat_classified_factors_exclude_empty_product
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul a (inv a p)) one)
    {a a' b b' : BHist} :
    RatHistoryClassifier a a' -> RatHistoryClassifier b b' ->
      (hsame (mul a b) BHist.Empty -> False) ∧
        (hsame (mul a' b') BHist.Empty -> False) := by
  intro classifiedA classifiedB
  have apartA := RatHistoryClassifier_endpoints_not_empty classifiedA
  have apartB := RatHistoryClassifier_endpoints_not_empty classifiedB
  have nonzeroTransport :
      forall {x y : BHist}, hsame x y ->
        (hsame x BHist.Empty -> False) -> (hsame y BHist.Empty -> False) := by
    intro x y sameXY apartX yEmpty
    exact apartX (hsame_trans sameXY yEmpty)
  have nonzeroEmptyAbsurd : (hsame BHist.Empty BHist.Empty -> False) -> False := by
    intro apartEmpty
    exact apartEmpty (hsame_refl BHist.Empty)
  constructor
  · exact field_nonzero_factors_exclude_empty_product
      (NonZero := fun h : BHist => hsame h BHist.Empty -> False) (inv := inv)
      addAssoc zeroLeft negLeft assocC leftId rightId addCongr mulCongr leftDistrib
      rightDistrib leftInv rightInv nonzeroTransport nonzeroEmptyAbsurd apartA.left apartB.left
  · exact field_nonzero_factors_exclude_empty_product
      (NonZero := fun h : BHist => hsame h BHist.Empty -> False) (inv := inv)
      addAssoc zeroLeft negLeft assocC leftId rightId addCongr mulCongr leftDistrib
      rightDistrib leftInv rightInv nonzeroTransport nonzeroEmptyAbsurd apartA.right
      apartB.right

end BEDC.Derived.FieldUp
