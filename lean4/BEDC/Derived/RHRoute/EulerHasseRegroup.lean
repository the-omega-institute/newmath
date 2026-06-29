import BEDC.Derived.RHRoute.EulerHasseEta
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.EulerHasseRegroup

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

def ratNat (n : Nat) : Rat :=
  BEDC.Real.RatNumKernel.ratNat n

def ratOfNatOverNat (num den : Nat) : Rat :=
  BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfNatOverNat num den

def twoPowWeight (n : Nat) : Rat :=
  ratOfNatOverNat 1 ((2 : Nat) ^ (Nat.succ n))

def binomialRat (n k : Nat) : Rat :=
  ratNat (BEDC.Derived.BinomialIdentitiesUp.C n k)

def signedBinomialWeight (n k : Nat) : Rat :=
  let c := binomialRat n k
  if k % 2 = 0 then
    ratMul (twoPowWeight n) c
  else
    ratNeg (ratMul (twoPowWeight n) c)

def sumRat : Nat -> (Nat -> Rat) -> Rat
  | 0, _ => ratZero
  | Nat.succ n, f => ratAdd (sumRat n f) (f n)

def sumComplex : Nat -> (Nat -> RatComplex) -> RatComplex
  | 0, _ => ratComplexZero
  | Nat.succ n, f => ratComplexAdd (sumComplex n f) (f n)

def etaCoeff (M m : Nat) : Rat :=
  if m = 0 then
    ratZero
  else
    sumRat M (fun n =>
      if m - 1 <= n then
        signedBinomialWeight n (m - 1)
      else
        ratZero)

def etaNested (M : Nat) (powNegS : Nat -> RatComplex) : RatComplex :=
  sumComplex M (fun n =>
    sumComplex (Nat.succ n) (fun k =>
      ratComplexScale (signedBinomialWeight n k) (powNegS (Nat.succ k))))

def etaGrouped (M : Nat) (powNegS : Nat -> RatComplex) : RatComplex :=
  sumComplex M (fun j =>
    ratComplexScale (etaCoeff M (Nat.succ j)) (powNegS (Nat.succ j)))

def RatComplexEq (z w : RatComplex) : Prop :=
  RatEq z.re w.re ∧ RatEq z.im w.im

theorem ratComplexEq_refl (z : RatComplex) :
    RatComplexEq z z := by
  exact ⟨RatEq_refl z.re, RatEq_refl z.im⟩

theorem ratComplexEq_symm {z w : RatComplex} :
    RatComplexEq z w -> RatComplexEq w z := by
  intro h
  exact ⟨RatEq_symm h.left, RatEq_symm h.right⟩

theorem ratComplexEq_trans (x y z : RatComplex) :
    RatComplexEq x y -> RatComplexEq y z -> RatComplexEq x z := by
  intro xy yz
  exact ⟨RatEq_trans x.re y.re z.re xy.left yz.left,
    RatEq_trans x.im y.im z.im xy.right yz.right⟩

theorem ratComplexAdd_congr {x x' y y' : RatComplex} :
    RatComplexEq x x' -> RatComplexEq y y' ->
      RatComplexEq (ratComplexAdd x y) (ratComplexAdd x' y') := by
  intro hx hy
  exact ⟨ratAdd_respects hx.left hy.left, ratAdd_respects hx.right hy.right⟩

theorem ratComplexScale_congr {a b : Rat} {z w : RatComplex} :
    RatEq a b -> RatComplexEq z w ->
      RatComplexEq (ratComplexScale a z) (ratComplexScale b w) := by
  intro hab hzw
  exact ⟨ratMul_respects hab hzw.left, ratMul_respects hab hzw.right⟩

theorem ratComplexAdd_assoc (x y z : RatComplex) :
    RatComplexEq (ratComplexAdd (ratComplexAdd x y) z)
      (ratComplexAdd x (ratComplexAdd y z)) := by
  exact ⟨BEDC.Derived.LocatedReal.ratAdd_assoc_local x.re y.re z.re,
    BEDC.Derived.LocatedReal.ratAdd_assoc_local x.im y.im z.im⟩

theorem ratComplexAdd_comm (x y : RatComplex) :
    RatComplexEq (ratComplexAdd x y) (ratComplexAdd y x) := by
  exact ⟨ratAdd_comm x.re y.re, ratAdd_comm x.im y.im⟩

theorem ratComplexAdd_zero_right (x : RatComplex) :
    RatComplexEq (ratComplexAdd x ratComplexZero) x := by
  exact ⟨ratAdd_zero_right x.re, ratAdd_zero_right x.im⟩

theorem ratComplexZero_add_left (x : RatComplex) :
    RatComplexEq (ratComplexAdd ratComplexZero x) x := by
  exact ⟨ratZero_add_left x.re, ratZero_add_left x.im⟩

private theorem ratMul_add_left_local (a b c : Rat) :
    RatEq (ratMul a (ratAdd b c))
      (ratAdd (ratMul a b) (ratMul a c)) :=
  BEDC.Real.RatNumKernel.ratMul_add_left a b c

private theorem ratMul_add_right_local (a b c : Rat) :
    RatEq (ratMul (ratAdd a b) c)
      (ratAdd (ratMul a c) (ratMul b c)) :=
  BEDC.Real.RatNumKernel.ratMul_add_right a b c

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change IntEq
    (IntMul (IntMul intZero x.num)
      (ratDenInt (intToRat intZero)))
    (IntMul intZero
      (ratDenInt
        { num := IntMul intZero x.num
          den := BEDC.Derived.IntUp.natMulFn
            (intToRat intZero).den x.den
          den_pos := ratDenPosMul (intToRat intZero).den_pos x.den_pos }))
  exact IntEq_trans
    (intMul_right_congr (c := ratDenInt (intToRat intZero))
      (intMul_zero_left x.num))
    (IntEq_symm (intMul_zero_left _))

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans _ _ _ (ratMul_comm x ratZero) (ratMul_zero_left_local x)

theorem ratComplexScale_add (a : Rat) (x y : RatComplex) :
    RatComplexEq (ratComplexScale a (ratComplexAdd x y))
      (ratComplexAdd (ratComplexScale a x) (ratComplexScale a y)) := by
  exact ⟨ratMul_add_left_local a x.re y.re,
    ratMul_add_left_local a x.im y.im⟩

theorem ratComplexScale_add_coeff (a b : Rat) (z : RatComplex) :
    RatComplexEq (ratComplexScale (ratAdd a b) z)
      (ratComplexAdd (ratComplexScale a z) (ratComplexScale b z)) := by
  exact ⟨ratMul_add_right_local a b z.re,
    ratMul_add_right_local a b z.im⟩

theorem ratComplexScale_zero (z : RatComplex) :
    RatComplexEq (ratComplexScale ratZero z) ratComplexZero := by
  exact ⟨ratMul_zero_left_local z.re, ratMul_zero_left_local z.im⟩

theorem ratComplexScale_zero_complex (a : Rat) :
    RatComplexEq (ratComplexScale a ratComplexZero) ratComplexZero := by
  exact ⟨ratMul_zero_right_local a, ratMul_zero_right_local a⟩

theorem sumComplex_congr {M : Nat} {f g : Nat -> RatComplex} :
    (∀ n : Nat, RatComplexEq (f n) (g n)) ->
      RatComplexEq (sumComplex M f) (sumComplex M g) := by
  intro h
  induction M with
  | zero =>
      exact ratComplexEq_refl ratComplexZero
  | succ M ih =>
      exact ratComplexAdd_congr ih (h M)

theorem sumRat_congr {M : Nat} {f g : Nat -> Rat} :
    (∀ n : Nat, RatEq (f n) (g n)) ->
      RatEq (sumRat M f) (sumRat M g) := by
  intro h
  induction M with
  | zero =>
      exact RatEq_refl ratZero
  | succ M ih =>
      exact ratAdd_respects ih (h M)

theorem sumComplex_add (M : Nat) (f g : Nat -> RatComplex) :
    RatComplexEq
      (sumComplex M (fun n => ratComplexAdd (f n) (g n)))
      (ratComplexAdd (sumComplex M f) (sumComplex M g)) := by
  induction M with
  | zero =>
      exact ratComplexEq_symm (ratComplexZero_add_left ratComplexZero)
  | succ M ih =>
      change RatComplexEq
        (ratComplexAdd
          (sumComplex M (fun n => ratComplexAdd (f n) (g n)))
          (ratComplexAdd (f M) (g M)))
        (ratComplexAdd
          (ratComplexAdd (sumComplex M f) (f M))
          (ratComplexAdd (sumComplex M g) (g M)))
      have step1 :
          RatComplexEq
            (ratComplexAdd
              (sumComplex M (fun n => ratComplexAdd (f n) (g n)))
              (ratComplexAdd (f M) (g M)))
            (ratComplexAdd
              (ratComplexAdd (sumComplex M f) (sumComplex M g))
              (ratComplexAdd (f M) (g M))) :=
        ratComplexAdd_congr ih (ratComplexEq_refl _)
      have step2 :
          RatComplexEq
            (ratComplexAdd
              (ratComplexAdd (sumComplex M f) (sumComplex M g))
              (ratComplexAdd (f M) (g M)))
            (ratComplexAdd
              (ratComplexAdd (sumComplex M f) (f M))
              (ratComplexAdd (sumComplex M g) (g M))) := by
        exact ratComplexEq_trans _ _ _
          (ratComplexAdd_assoc (sumComplex M f) (sumComplex M g)
            (ratComplexAdd (f M) (g M)))
          (ratComplexEq_trans _ _ _
            (ratComplexAdd_congr (ratComplexEq_refl _)
              (ratComplexEq_symm (ratComplexAdd_assoc (sumComplex M g) (f M) (g M))))
            (ratComplexEq_trans _ _ _
              (ratComplexAdd_congr (ratComplexEq_refl _)
                (ratComplexAdd_congr
                  (ratComplexAdd_comm (sumComplex M g) (f M))
                  (ratComplexEq_refl _)))
              (ratComplexEq_trans _ _ _
                (ratComplexAdd_congr (ratComplexEq_refl _)
                  (ratComplexAdd_assoc (f M) (sumComplex M g) (g M)))
                (ratComplexEq_symm
                  (ratComplexAdd_assoc (sumComplex M f) (f M)
                    (ratComplexAdd (sumComplex M g) (g M)))))))
      exact ratComplexEq_trans _ _ _ step1 step2

theorem sumComplex_scale_left (M : Nat) (a : Rat) (f : Nat -> RatComplex) :
    RatComplexEq
      (ratComplexScale a (sumComplex M f))
      (sumComplex M (fun n => ratComplexScale a (f n))) := by
  induction M with
  | zero =>
      exact ratComplexScale_zero_complex a
  | succ M ih =>
      change RatComplexEq
        (ratComplexScale a (ratComplexAdd (sumComplex M f) (f M)))
        (ratComplexAdd
          (sumComplex M (fun n => ratComplexScale a (f n)))
          (ratComplexScale a (f M)))
      exact ratComplexEq_trans _ _ _
        (ratComplexScale_add a (sumComplex M f) (f M))
        (ratComplexAdd_congr ih (ratComplexEq_refl _))

theorem sumComplex_scale_coeff (M : Nat) (a b : Nat -> Rat) (z : Nat -> RatComplex) :
    RatComplexEq
      (sumComplex M (fun n => ratComplexScale (ratAdd (a n) (b n)) (z n)))
      (ratComplexAdd
        (sumComplex M (fun n => ratComplexScale (a n) (z n)))
        (sumComplex M (fun n => ratComplexScale (b n) (z n)))) := by
  exact ratComplexEq_trans _ _ _
    (sumComplex_congr (M := M) (fun n => ratComplexScale_add_coeff (a n) (b n) (z n)))
    (sumComplex_add M (fun n => ratComplexScale (a n) (z n))
      (fun n => ratComplexScale (b n) (z n)))

def rowTail (N m : Nat) (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) : RatComplex :=
  sumComplex N (fun n => ratComplexScale (w n m) (z m))

def triangularNestedFrom (M N : Nat)
    (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) : RatComplex :=
  sumComplex M (fun n => sumComplex (n + N) (fun k => ratComplexScale (w n k) (z k)))

def triangularGroupedFrom (M N : Nat)
    (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) : RatComplex :=
  sumComplex (M + N) (fun k =>
    ratComplexScale (sumRat M (fun n => if k < n + N then w n k else ratZero)) (z k))

theorem sumRat_if_lt_succ_self (N k : Nat) (w : Nat -> Nat -> Rat) :
    RatEq
      (sumRat N (fun n => if k < n then w n k else ratZero))
      (sumRat N (fun n => if Nat.succ k < Nat.succ n then w n k else ratZero)) := by
  apply sumRat_congr
  intro n
  by_cases h : k < n
  · have hs : Nat.succ k < Nat.succ n := Nat.succ_lt_succ h
    rw [if_pos h, if_pos hs]
    exact RatEq_refl _
  · have hs : ¬ Nat.succ k < Nat.succ n := by
      intro bad
      exact h (Nat.lt_of_succ_lt_succ bad)
    rw [if_neg h, if_neg hs]
    exact RatEq_refl _

theorem row_succ_column_split (N : Nat)
    (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) :
    RatComplexEq
      (sumComplex (Nat.succ N) (fun k => ratComplexScale (w N k) (z k)))
      (ratComplexAdd
        (sumComplex N (fun k => ratComplexScale (w N k) (z k)))
        (ratComplexScale (w N N) (z N))) := by
  exact ratComplexEq_refl _

theorem sumRat_all_zero {M : Nat} {f : Nat -> Rat} :
    (∀ n : Nat, n < M -> RatEq (f n) ratZero) ->
      RatEq (sumRat M f) ratZero := by
  intro h
  induction M with
  | zero =>
      exact RatEq_refl ratZero
  | succ M ih =>
      change RatEq (ratAdd (sumRat M f) (f M)) ratZero
      exact RatEq_trans _ _ _
        (ratAdd_respects
          (ih (fun n hn => h n (Nat.lt_trans hn (Nat.lt_succ_self M))))
          (h M (Nat.lt_succ_self M)))
        (ratAdd_zero_right ratZero)

theorem sumComplex_congr_lt {M : Nat} {f g : Nat -> RatComplex} :
    (∀ n : Nat, n < M -> RatComplexEq (f n) (g n)) ->
      RatComplexEq (sumComplex M f) (sumComplex M g) := by
  intro h
  induction M with
  | zero =>
      exact ratComplexEq_refl ratComplexZero
  | succ M ih =>
      change RatComplexEq
        (ratComplexAdd (sumComplex M f) (f M))
        (ratComplexAdd (sumComplex M g) (g M))
      exact ratComplexAdd_congr
        (ih (fun n hn => h n (Nat.lt_trans hn (Nat.lt_succ_self M))))
        (h M (Nat.lt_succ_self M))

theorem coeff_succ_of_lt (M j : Nat) (w : Nat -> Nat -> Rat)
    (hj : j < M) :
    RatEq
      (sumRat (Nat.succ M) (fun n => if j <= n then w n j else ratZero))
      (ratAdd (sumRat M (fun n => if j <= n then w n j else ratZero)) (w M j)) := by
  change RatEq
    (ratAdd (sumRat M (fun n => if j <= n then w n j else ratZero))
      (if j <= M then w M j else ratZero))
    (ratAdd (sumRat M (fun n => if j <= n then w n j else ratZero)) (w M j))
  have hle : j <= M := Nat.le_of_lt hj
  rw [if_pos hle]
  exact RatEq_refl _

theorem coeff_succ_last (M : Nat) (w : Nat -> Nat -> Rat) :
    RatEq
      (sumRat (Nat.succ M) (fun n => if M <= n then w n M else ratZero))
      (w M M) := by
  change RatEq
    (ratAdd (sumRat M (fun n => if M <= n then w n M else ratZero))
      (if M <= M then w M M else ratZero))
    (w M M)
  rw [if_pos (Nat.le_refl M)]
  have prefixZero :
      RatEq (sumRat M (fun n => if M <= n then w n M else ratZero)) ratZero := by
    apply sumRat_all_zero
    intro n hn
    have notLe : ¬ M <= n := Nat.not_le_of_gt hn
    rw [if_neg notLe]
    exact RatEq_refl ratZero
  exact RatEq_trans _ _ _
    (ratAdd_respects prefixZero (RatEq_refl (w M M)))
    (ratZero_add_left (w M M))

theorem grouped_succ_step (M : Nat)
    (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) :
    RatComplexEq
      (ratComplexAdd
        (sumComplex M (fun j =>
          ratComplexScale
            (sumRat M (fun n => if j <= n then w n j else ratZero))
            (z j)))
        (sumComplex (Nat.succ M) (fun j => ratComplexScale (w M j) (z j))))
      (sumComplex (Nat.succ M) (fun j =>
        ratComplexScale
          (sumRat (Nat.succ M) (fun n => if j <= n then w n j else ratZero))
          (z j))) := by
  change RatComplexEq
    (ratComplexAdd
      (sumComplex M (fun j =>
        ratComplexScale
          (sumRat M (fun n => if j <= n then w n j else ratZero))
          (z j)))
      (ratComplexAdd
        (sumComplex M (fun j => ratComplexScale (w M j) (z j)))
        (ratComplexScale (w M M) (z M))))
    (ratComplexAdd
      (sumComplex M (fun j =>
        ratComplexScale
          (sumRat (Nat.succ M) (fun n => if j <= n then w n j else ratZero))
          (z j)))
      (ratComplexScale
        (sumRat (Nat.succ M) (fun n => if M <= n then w n M else ratZero))
        (z M)))
  have oldColumns :
      RatComplexEq
        (sumComplex M (fun j =>
          ratComplexScale
            (sumRat (Nat.succ M) (fun n => if j <= n then w n j else ratZero))
            (z j)))
        (sumComplex M (fun j =>
          ratComplexScale
            (ratAdd
              (sumRat M (fun n => if j <= n then w n j else ratZero))
              (w M j))
            (z j))) := by
    apply sumComplex_congr_lt
    intro j hj
    exact ratComplexScale_congr (coeff_succ_of_lt M j w hj) (ratComplexEq_refl _)
  have splitColumns :
      RatComplexEq
        (sumComplex M (fun j =>
          ratComplexScale
            (ratAdd
              (sumRat M (fun n => if j <= n then w n j else ratZero))
              (w M j))
            (z j)))
        (ratComplexAdd
          (sumComplex M (fun j =>
            ratComplexScale
              (sumRat M (fun n => if j <= n then w n j else ratZero))
              (z j)))
          (sumComplex M (fun j => ratComplexScale (w M j) (z j)))) :=
    sumComplex_scale_coeff M
      (fun j => sumRat M (fun n => if j <= n then w n j else ratZero))
      (fun j => w M j)
      z
  have lastColumn :
      RatComplexEq
        (ratComplexScale
          (sumRat (Nat.succ M) (fun n => if M <= n then w n M else ratZero))
          (z M))
        (ratComplexScale (w M M) (z M)) :=
    ratComplexScale_congr (coeff_succ_last M w) (ratComplexEq_refl _)
  exact ratComplexEq_symm
    (ratComplexEq_trans _ _ _
      (ratComplexAdd_congr oldColumns lastColumn)
      (ratComplexEq_trans _ _ _
        (ratComplexAdd_congr splitColumns (ratComplexEq_refl _))
        (ratComplexAdd_assoc
          (sumComplex M (fun j =>
            ratComplexScale
              (sumRat M (fun n => if j <= n then w n j else ratZero))
              (z j)))
          (sumComplex M (fun j => ratComplexScale (w M j) (z j)))
          (ratComplexScale (w M M) (z M)))))

theorem triangular_regroup_from_zero
    (M : Nat) (w : Nat -> Nat -> Rat) (z : Nat -> RatComplex) :
    RatComplexEq
      (sumComplex M (fun n =>
        sumComplex (Nat.succ n) (fun k => ratComplexScale (w n k) (z k))))
      (sumComplex M (fun j =>
        ratComplexScale
          (sumRat M (fun n => if j <= n then w n j else ratZero))
          (z j))) := by
  induction M with
  | zero =>
      exact ratComplexEq_refl ratComplexZero
  | succ M ih =>
      change RatComplexEq
        (ratComplexAdd
          (sumComplex M (fun n =>
            sumComplex (Nat.succ n) (fun k => ratComplexScale (w n k) (z k))))
          (sumComplex (Nat.succ M) (fun k => ratComplexScale (w M k) (z k))))
        (sumComplex (Nat.succ M) (fun j =>
          ratComplexScale
            (sumRat (Nat.succ M) (fun n => if j <= n then w n j else ratZero))
            (z j)))
      exact ratComplexEq_trans _ _ _
        (ratComplexAdd_congr ih (ratComplexEq_refl _))
        (grouped_succ_step M w z)

theorem eta_nested_eq_grouped (M : Nat) (powNegS : Nat -> RatComplex) :
    RatComplexEq (etaNested M powNegS) (etaGrouped M powNegS) := by
  unfold etaNested etaGrouped etaCoeff
  exact triangular_regroup_from_zero M signedBinomialWeight (fun k => powNegS (Nat.succ k))

end BEDC.Derived.RHRoute.EulerHasseRegroup
