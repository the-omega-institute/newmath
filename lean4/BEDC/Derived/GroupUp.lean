import BEDC.FKernel.Hist
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

theorem group_stability_certificate_fields {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b'}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (invCongr : ∀ {a b}, hsame a b → hsame (inv a) (inv b))
    (leftInv : ∀ x, hsame (mul (inv x) x) e)
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ((∀ x : BHist, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x x) ∧
      (∀ {x y z : BHist}, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x y →
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame y z →
          BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x z) ∧
      (∀ x y z : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame
          (mul (mul x y) z) (mul x (mul y z))) ∧
      (∀ x : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul e x) x) ∧
      (∀ x : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul x e) x) ∧
      (∀ {a a' b b' : BHist}, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame a a' →
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame b b' →
          BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul a b) (mul a' b'))) ∧
      (∀ {a b : BHist}, hsame a b → hsame (inv a) (inv b)) ∧
      (∀ x : BHist, hsame (mul (inv x) x) e) ∧
      (∀ x : BHist, hsame (mul x (inv x)) e) := by
  constructor
  · exact BEDC.Derived.MonoidUp.monoid_stability_certificate_fields
      BEDC.FKernel.Hist.hsame_refl
      BEDC.FKernel.Hist.hsame_trans
      assocC
      leftId
      rightId
      mulCongr
  · constructor
    · intro a b same
      exact invCongr same
    · constructor
      · intro x
        exact leftInv x
      · intro x
        exact rightInv x

theorem group_inverse_identity {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (rightId : forall x : BHist, hsame (mul x e) x)
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e) :
    hsame (inv e) e := by
  exact hsame_trans (hsame_symm (rightId (inv e))) (leftInv e)

theorem group_left_inverse_involutive {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (leftInv : ∀ x, hsame (mul (inv x) x) e) :
    ∀ x : BHist, hsame (inv (inv x)) x := by
  intro x
  exact hsame_trans (hsame_symm (rightId (inv (inv x))))
    (hsame_trans
      (mulCongr (hsame_refl (inv (inv x))) (hsame_symm (leftInv x)))
      (hsame_trans (hsame_symm (assocC (inv (inv x)) (inv x) x))
        (hsame_trans (mulCongr (leftInv (inv x)) (hsame_refl x)) (leftId x))))

theorem group_right_inverse_involutive {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ∀ x : BHist, hsame (inv (inv x)) x := by
  intro x
  exact hsame_trans (hsame_symm (leftId (inv (inv x))))
    (hsame_trans
      (mulCongr (hsame_symm (rightInv x)) (hsame_refl (inv (inv x))))
      (hsame_trans (assocC x (inv x) (inv (inv x)))
        (hsame_trans
          (mulCongr (hsame_refl x) (rightInv (inv x)))
          (rightId x))))

theorem group_left_right_inverse_uniqueness {mul : BHist → BHist → BHist} {e : BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    {x y z : BHist} :
    hsame (mul y x) e → hsame (mul x z) e → hsame y z := by
  intro left right
  exact hsame_trans (hsame_symm (rightId y))
    (hsame_trans
      (mulCongr (hsame_refl y) (hsame_symm right))
      (hsame_trans (hsame_symm (assocC y x z))
        (hsame_trans (mulCongr left (hsame_refl z)) (leftId z))))

theorem group_inverse_congruence_from_laws {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (leftInv : ∀ x, hsame (mul (inv x) x) e)
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ∀ {x y : BHist}, hsame x y → hsame (inv x) (inv y) := by
  intro x y same
  exact group_left_right_inverse_uniqueness assocC leftId rightId mulCongr
    (hsame_trans
      (hsame_symm (mulCongr (hsame_refl (inv x)) same))
      (leftInv x))
    (rightInv y)

theorem group_inverse_mul_reverse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall x y : BHist, hsame (inv (mul x y)) (mul (inv y) (inv x)) := by
  intro x y
  have reverseRight : hsame (mul (mul x y) (mul (inv y) (inv x))) e := by
    have inner :
        hsame (mul y (mul (inv y) (inv x))) (inv x) := by
      exact hsame_trans (hsame_symm (assocC y (inv y) (inv x)))
        (hsame_trans (mulCongr (rightInv y) (hsame_refl (inv x)))
          (leftId (inv x)))
    exact hsame_trans (assocC x y (mul (inv y) (inv x)))
      (hsame_trans (mulCongr (hsame_refl x) inner) (rightInv x))
  exact group_left_right_inverse_uniqueness assocC leftId rightId mulCongr
    (leftInv (mul x y))
    reverseRight

theorem group_inverse_cancel_from_laws {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall {x y : BHist}, hsame (inv x) (inv y) -> hsame x y := by
  intro x y sameInv
  have sameDouble :
      hsame (inv (inv x)) (inv (inv y)) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv
      sameInv
  exact hsame_trans
    (hsame_symm (group_left_inverse_involutive assocC leftId rightId mulCongr leftInv x))
    (hsame_trans sameDouble
      (group_left_inverse_involutive assocC leftId rightId mulCongr leftInv y))

theorem group_left_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b c : BHist} :
    hsame (mul a b) (mul a c) -> hsame b c := by
  intro sameProducts
  exact hsame_trans (hsame_symm (leftId b))
    (hsame_trans (mulCongr (hsame_symm (leftInv a)) (hsame_refl b))
      (hsame_trans (assocC (inv a) a b)
        (hsame_trans (mulCongr (hsame_refl (inv a)) sameProducts)
          (hsame_trans (hsame_symm (assocC (inv a) a c))
            (hsame_trans (mulCongr (leftInv a) (hsame_refl c)) (leftId c))))))

theorem group_left_absorb_right_factor_unit {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b : BHist} :
    hsame (mul a b) a -> hsame b e := by
  intro absorb
  exact group_left_cancel assocC leftId mulCongr leftInv
    (hsame_trans absorb (hsame_symm (rightId a)))

theorem group_right_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) e) {a b c : BHist} :
    hsame (mul b a) (mul c a) -> hsame b c := by
  intro sameProducts
  exact hsame_trans (hsame_symm (rightId b))
    (hsame_trans (mulCongr (hsame_refl b) (hsame_symm (rightInv a)))
      (hsame_trans (hsame_symm (assocC b a (inv a)))
        (hsame_trans (mulCongr sameProducts (hsame_refl (inv a)))
          (hsame_trans (assocC c a (inv a))
            (hsame_trans (mulCongr (hsame_refl c) (rightInv a)) (rightId c))))))

theorem group_two_sided_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e)
    (rightInv : forall x, hsame (mul x (inv x)) e) {a b c d : BHist} :
    hsame (mul (mul a b) c) (mul (mul a d) c) -> hsame b d := by
  intro sameProducts
  have sameLeftProducts : hsame (mul a b) (mul a d) :=
    group_right_cancel assocC rightId mulCongr rightInv sameProducts
  exact group_left_cancel assocC leftId mulCongr leftInv sameLeftProducts

theorem group_left_right_inverse_unique {mul : BHist → BHist → BHist} {e : BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    {x y z : BHist} :
    hsame (mul y x) e → hsame (mul x z) e → hsame y z := by
  intro leftInv rightInv
  exact hsame_trans (hsame_symm (rightId y))
    (hsame_trans (mulCongr (hsame_refl y) (hsame_symm rightInv))
      (hsame_trans (hsame_symm (assocC y x z))
        (hsame_trans (mulCongr leftInv (hsame_refl z)) (leftId z))))

end BEDC.Derived.GroupUp
