import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

def CommRingApartZero (x : BHist) : Prop :=
  hsame x BHist.Empty -> False

def CommRingLeftZeroDivisor (mul : BHist -> BHist -> BHist) (x : BHist) : Prop :=
  CommRingApartZero x ∧
    Exists (fun c : BHist => CommRingApartZero c ∧ hsame (mul x c) BHist.Empty)

theorem CommRingLeftZeroDivisor_product_closed {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    CommRingLeftZeroDivisor mul a ->
      CommRingApartZero (mul a b) ->
        CommRingLeftZeroDivisor mul (mul a b) := by
  intro leftZD productApart
  cases leftZD.right with
  | intro c data =>
      have rightDistrib : forall x y z : BHist,
          hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
        exact commring_right_distrib_from_left mulComm addCongr leftDistrib
      have zeroAbsorption :
          And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
            (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
        BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
          addCongr mulCongr leftDistrib rightDistrib
      have sameReassoc :
          hsame (mul (mul a b) c) (mul a (mul c b)) := by
        exact hsame_trans (mulAssoc a b c)
          (mulCongr (hsame_refl a) (mulComm b c))
      have sameToLeftProduct :
          hsame (mul a (mul c b)) (mul (mul a c) b) := by
        exact hsame_symm (mulAssoc a c b)
      have leftProductZero : hsame (mul (mul a c) b) BHist.Empty := by
        exact hsame_trans
          (mulCongr data.right (hsame_refl b))
          (zeroAbsorption.right b)
      constructor
      · exact productApart
      · exact Exists.intro c
          (And.intro data.left
            (hsame_trans sameReassoc
              (hsame_trans sameToLeftProduct leftProductZero)))

end BEDC.Derived.CommRingUp
