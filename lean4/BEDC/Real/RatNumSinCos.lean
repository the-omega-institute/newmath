import BEDC.Real.RatNumTrig

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumSinCos

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumTrig

abbrev Rat : Type :=
  RatNumKernel.Rat

def factorialNat : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorialNat n

theorem factorialNat_pos (n : Nat) :
    0 < factorialNat n := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      change 0 < Nat.succ n * factorialNat n
      exact Nat.mul_pos (Nat.succ_pos n) ih

private theorem factorialNat_step_le (n : Nat) :
    factorialNat n ≤ factorialNat (n + 1) := by
  cases n with
  | zero =>
      decide
  | succ n =>
      change Nat.succ n * factorialNat n ≤
        Nat.succ (Nat.succ n) * factorialNat (Nat.succ n)
      have hleft :
          Nat.succ n * factorialNat n ≤
            Nat.succ (Nat.succ n) * factorialNat n :=
        Nat.mul_le_mul_right (factorialNat n)
          (Nat.le_succ (Nat.succ n))
      have hright :
          Nat.succ (Nat.succ n) * factorialNat n ≤
            Nat.succ (Nat.succ n) * (Nat.succ n * factorialNat n) := by
        apply Nat.mul_le_mul_left
        exact Nat.le_mul_of_pos_left (factorialNat n) (Nat.succ_pos n)
      exact Nat.le_trans hleft hright

private theorem factorialNat_le_add
    (m d : Nat) :
    factorialNat m ≤ factorialNat (m + d) := by
  induction d with
  | zero =>
      rw [Nat.add_zero]
      exact Nat.le_refl (factorialNat m)
  | succ d ih =>
      rw [Nat.add_succ]
      exact Nat.le_trans ih (factorialNat_step_le (m + d))

private theorem factorialNat_mono_of_le {m n : Nat}
    (h : m ≤ n) :
    factorialNat m ≤ factorialNat n := by
  cases Nat.le.dest h with
  | intro d hd =>
      rw [← hd]
      exact factorialNat_le_add m d

private theorem factorialNat_self_le
    (n : Nat) :
    n ≤ factorialNat n := by
  cases n with
  | zero =>
      decide
  | succ n =>
      change Nat.succ n ≤ Nat.succ n * factorialNat n
      exact Nat.le_mul_of_pos_right (Nat.succ n) (factorialNat_pos n)

def factDen (n : Nat) : Rat :=
  ratNat (factorialNat n)

theorem factDen_pos (n : Nat) :
    ratLt ratZero (factDen n) := by
  unfold factDen
  exact RatNumTrig.ratNat_pos_of_pos (factorialNat_pos n)

theorem factDen_apart (n : Nat) :
    ratApart0 (factDen n) :=
  ratApart0_of_pos (factDen_pos n)

theorem factDen_le_of_nat_le {m n : Nat}
    (h : m ≤ n) :
    ratLe (factDen m) (factDen n) := by
  unfold factDen
  exact ratNat_le_of_nat_le (factorialNat_mono_of_le h)

def factDiv (x : Rat) (n : Nat) : Rat :=
  ratDivApart x (factDen n) (factDen_apart n)

theorem factTailDen_apart
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (n : Nat) :
    ratApart0
      (ratMul (factDen n)
        (ratSub ratOne (ratMul theta theta))) :=
  ratMul_apart0 (factDen_apart n)
    (one_sub_sq_apart theta h0 h1)

def factorialTailBound
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (n : Nat) : Rat :=
  ratDivApart
    (ratPow theta n)
    (ratMul (factDen n)
      (ratSub ratOne (ratMul theta theta)))
    (factTailDen_apart theta h0 h1 n)

def factorialTailAbs (theta : Rat) (n K : Nat) : Rat :=
  ratSum K (fun j => factDiv (ratPow theta (n + 2 * j)) (n + 2 * j))

def signedTermFromAbs (absTerm : Nat -> Rat) (k : Nat) : Rat :=
  if k % 2 = 0 then absTerm k else ratNeg (absTerm k)

def sinAbsTerm (theta : Rat) (k : Nat) : Rat :=
  factDiv (ratPow theta (2 * k + 1)) (2 * k + 1)

def cosAbsTerm (theta : Rat) (k : Nat) : Rat :=
  factDiv (ratPow theta (2 * k)) (2 * k)

def sinTerm (theta : Rat) (k : Nat) : Rat :=
  signedTermFromAbs (sinAbsTerm theta) k

def cosTerm (theta : Rat) (k : Nat) : Rat :=
  signedTermFromAbs (cosAbsTerm theta) k

def sinPart (theta : Rat) (M : Nat) : Rat :=
  ratSum M (sinTerm theta)

def cosPart (theta : Rat) (M : Nat) : Rat :=
  ratSum M (cosTerm theta)

def sinTailBound
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  factorialTailBound theta h0 h1 (2 * M + 1)

def cosTailBound
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  factorialTailBound theta h0 h1 (2 * M)

def sinLo
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  ratSub (sinPart theta M) (sinTailBound theta h0 h1 M)

def sinHi
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  ratAdd (sinPart theta M) (sinTailBound theta h0 h1 M)

def cosLo
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  ratSub (cosPart theta M) (cosTailBound theta h0 h1 M)

def cosHi
    (theta : Rat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M : Nat) : Rat :=
  ratAdd (cosPart theta M) (cosTailBound theta h0 h1 M)

def sinTailSigned (theta : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => sinTerm theta (M + j))

def cosTailSigned (theta : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => cosTerm theta (M + j))

def sinAbsTail (theta : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => sinAbsTerm theta (M + j))

def cosAbsTail (theta : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => cosAbsTerm theta (M + j))

theorem ratDivApart_le_same_num_den_mono
    {x a b : Rat}
    (hx : ratLe ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLe a b) :
    ratLe (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    ratDivApart_mul_cancel_right haApart
  have divBNonneg :
      ratLe ratZero (ratDivApart x b hbApart) :=
    ratDivApart_nonneg_of_nonneg_pos hx hb hbApart
  have step :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) :=
    ratMul_le_mul_nonneg_left hab divBNonneg
  have toX :
      ratLe (ratMul (ratDivApart x b hbApart) a) x :=
    ratLe_of_RatEq_right step leftCancel
  have targetMul :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    ratLe_of_RatEq_right toX (RatEq_symm rightCancel)
  exact ratMul_le_cancel_right ha targetMul

theorem factDiv_le_factDiv
    {x y : Rat}
    {m n : Nat}
    (hxy : ratLe x y)
    (hx : ratLe ratZero x)
    (hmn : m ≤ n) :
    ratLe (factDiv x n) (factDiv y m) := by
  have yNonneg : ratLe ratZero y :=
    ratLe_trans hx hxy
  have first :
      ratLe (factDiv x n) (factDiv x m) := by
    unfold factDiv
    exact ratDivApart_le_same_num_den_mono hx
      (factDen_pos m)
      (factDen_pos n)
      (factDen_apart m)
      (factDen_apart n)
      (factDen_le_of_nat_le hmn)
  have invNonneg :
      ratLe ratZero (ratInvApart (factDen m) (factDen_apart m)) := by
    have raw :
        ratLe ratZero (ratDivApart ratOne (factDen m) (factDen_apart m)) :=
      ratDivApart_nonneg_of_nonneg_pos
        (by
          change ratLe ratZero ratOne
          apply ratNonneg_of_num
          unfold ratOne intToRat intOne intOfNat
          exact intLe_zero_of_nat NatOne (unary_e1_closed unary_empty))
        (factDen_pos m)
        (factDen_apart m)
    change ratLe ratZero (ratMul ratOne (ratInvApart (factDen m) (factDen_apart m))) at raw
    exact ratLe_of_RatEq_right raw
      (ratOne_mul_left (ratInvApart (factDen m) (factDen_apart m)))
  have second :
      ratLe (factDiv x m) (factDiv y m) := by
    unfold factDiv ratDivApart
    exact ratMul_le_mul_right hxy invNonneg
  exact ratLe_trans first second

private theorem ratPow_even_tail_split (theta : Rat) (n j : Nat) :
    RatEq (ratPow theta (n + 2 * j))
      (ratMul (ratPow theta n)
        (ratPow (ratMul theta theta) j)) :=
  RatEq_trans _ _ _
    (ratPow_add theta n (2 * j))
    (ratMul_respects (RatEq_refl (ratPow theta n))
      (ratPow_sq_base theta j))

theorem factorialTerm_le_scaled_geom_term
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (n j : Nat) :
    ratLe
      (factDiv (ratPow theta (n + 2 * j)) (n + 2 * j))
      (ratMul
        (factDiv (ratPow theta n) n)
        (ratPow (ratMul theta theta) j)) := by
  unfold factDiv
  let x := ratPow theta (n + 2 * j)
  let y :=
    ratMul (ratPow theta n)
      (ratPow (ratMul theta theta) j)
  have xy : RatEq x y := by
    unfold x y
    exact ratPow_even_tail_split theta n j
  have yNonneg : ratLe ratZero y := by
    unfold y
    exact ratMul_nonneg
      (ratPow_nonneg h0 n)
      (ratPow_nonneg (ratMul_nonneg h0 h0) j)
  have divLe :
      ratLe
        (ratDivApart y (factDen (n + 2 * j))
          (factDen_apart (n + 2 * j)))
        (ratDivApart y (factDen n) (factDen_apart n)) := by
    exact ratDivApart_le_same_num_den_mono yNonneg
      (factDen_pos n)
      (factDen_pos (n + 2 * j))
      (factDen_apart n)
      (factDen_apart (n + 2 * j))
      (factDen_le_of_nat_le (Nat.le_add_right n (2 * j)))
  have leftEq :
      RatEq
        (ratDivApart x (factDen (n + 2 * j))
          (factDen_apart (n + 2 * j)))
        (ratDivApart y (factDen (n + 2 * j))
          (factDen_apart (n + 2 * j))) := by
    unfold ratDivApart
    exact ratMul_respects xy (RatEq_refl _)
  have rightEq :
      RatEq
        (ratDivApart y (factDen n) (factDen_apart n))
        (ratMul
          (ratDivApart (ratPow theta n) (factDen n)
            (factDen_apart n))
          (ratPow (ratMul theta theta) j)) := by
    unfold y ratDivApart
    exact RatEq_trans _ _ _
      (ratMul_assoc
        (ratPow theta n)
        (ratPow (ratMul theta theta) j)
        (ratInvApart (factDen n) (factDen_apart n)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratPow theta n))
          (ratMul_comm
            (ratPow (ratMul theta theta) j)
            (ratInvApart (factDen n) (factDen_apart n))))
        (RatEq_symm
          (ratMul_assoc
            (ratPow theta n)
            (ratInvApart (factDen n) (factDen_apart n))
            (ratPow (ratMul theta theta) j))))
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left leftEq divLe)
    rightEq

theorem factorialTailAbs_le_scaled_geom
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (n K : Nat) :
    ratLe (factorialTailAbs theta n K)
      (ratMul
        (factDiv (ratPow theta n) n)
        (geomSum (ratMul theta theta) K)) := by
  unfold factorialTailAbs geomSum
  let scale := factDiv (ratPow theta n) n
  let q := ratMul theta theta
  have termwise :
      ratLe
        (ratSum K
          (fun j => factDiv (ratPow theta (n + 2 * j))
            (n + 2 * j)))
        (ratSum K
          (fun j => ratMul scale (ratPow q j))) := by
    apply ratSum_le_sum
    intro j _hj
    unfold scale q
    exact factorialTerm_le_scaled_geom_term h0 n j
  have sumEq :
      RatEq
        (ratSum K (fun j => ratMul scale (ratPow q j)))
        (ratMul scale (ratSum K (fun j => ratPow q j))) :=
    RatEq_symm (ratMul_sum_left scale K (fun j => ratPow q j))
  exact ratLe_of_RatEq_right termwise sumEq

theorem factorialTailAbs_le_bound
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (n K : Nat) :
    ratLe
      (factorialTailAbs theta n K)
      (factorialTailBound theta h0 h1 n) := by
  let q := ratMul theta theta
  let A := ratPow theta n
  let d := factDen n
  let gap := ratSub ratOne q
  let hd : ratApart0 d := factDen_apart n
  let hgap : ratApart0 gap := one_sub_sq_apart theta h0 h1
  let hden : ratApart0 (ratMul d gap) :=
    factTailDen_apart theta h0 h1 n
  let scale := factDiv A n
  have hTailToGeom :
      ratLe (factorialTailAbs theta n K)
        (ratMul scale (geomSum q K)) := by
    unfold scale A q
    exact factorialTailAbs_le_scaled_geom h0 n K
  have hA_nonneg : ratLe ratZero A := by
    unfold A
    exact ratPow_nonneg h0 n
  have hScaleNonneg : ratLe ratZero scale := by
    unfold scale A factDiv
    exact ratDivApart_nonneg_of_nonneg_pos
      hA_nonneg
      (factDen_pos n)
      (factDen_apart n)
  have hqNonneg : ratLe ratZero q := by
    unfold q
    exact ratMul_nonneg h0 h0
  have hqLtOne : ratLt q ratOne := by
    unfold q
    exact sq_lt_one_of_nonneg_lt_one h0 h1
  have hGeom :
      ratLe (geomSum q K) (ratDivApart ratOne gap hgap) := by
    unfold gap hgap
    exact geomSum_le_inv_one_sub q hqNonneg hqLtOne K
      (one_sub_sq_apart theta h0 h1)
  have hScaled :
      ratLe
        (ratMul scale (geomSum q K))
        (ratMul scale (ratDivApart ratOne gap hgap)) :=
    ratMul_le_mul_nonneg_left hGeom hScaleNonneg
  have hCollapse :
      RatEq
        (ratMul scale (ratDivApart ratOne gap hgap))
        (ratDivApart A (ratMul d gap) hden) := by
    unfold scale factDiv A d
    exact ratDivApart_scaled_geom_collapse A d gap hd hgap hden
  unfold factorialTailBound
  exact ratLe_of_RatEq_right
    (ratLe_trans hTailToGeom hScaled)
    hCollapse

private theorem sin_index_split_nat (M j : Nat) :
    2 * (M + j) + 1 = 2 * M + 1 + 2 * j := by
  calc
    2 * (M + j) + 1 = (2 * M + 2 * j) + 1 := by
      rw [Nat.mul_add]
    _ = 2 * M + (2 * j + 1) := Nat.add_assoc (2 * M) (2 * j) 1
    _ = 2 * M + (1 + 2 * j) :=
      congrArg (fun t => 2 * M + t) (Nat.add_comm (2 * j) 1)
    _ = 2 * M + 1 + 2 * j :=
      (Nat.add_assoc (2 * M) 1 (2 * j)).symm

private theorem cos_index_split_nat (M j : Nat) :
    2 * (M + j) = 2 * M + 2 * j := by
  rw [Nat.mul_add]

private theorem evenPow_split (theta : Rat) (M j : Nat) :
    RatEq (ratPow theta (2 * (M + j)))
      (ratMul (ratPow theta (2 * M))
        (ratPow (ratMul theta theta) j)) := by
  rw [cos_index_split_nat M j]
  exact RatEq_trans _ _ _
    (ratPow_add theta (2 * M) (2 * j))
    (ratMul_respects (RatEq_refl (ratPow theta (2 * M)))
      (ratPow_sq_base theta j))

theorem sinAbsTerm_nonneg
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (k : Nat) :
    ratLe ratZero (sinAbsTerm theta k) := by
  unfold sinAbsTerm factDiv
  exact ratDivApart_nonneg_of_nonneg_pos
    (ratPow_nonneg h0 (2 * k + 1))
    (factDen_pos (2 * k + 1))
    (factDen_apart (2 * k + 1))

theorem cosAbsTerm_nonneg
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (k : Nat) :
    ratLe ratZero (cosAbsTerm theta k) := by
  unfold cosAbsTerm factDiv
  exact ratDivApart_nonneg_of_nonneg_pos
    (ratPow_nonneg h0 (2 * k))
    (factDen_pos (2 * k))
    (factDen_apart (2 * k))

theorem sinAbsTerm_le_scaled_geom_term
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M j : Nat) :
    ratLe (sinAbsTerm theta (M + j))
      (ratMul
        (factDiv (ratPow theta (2 * M + 1)) (2 * M + 1))
        (ratPow (ratMul theta theta) j)) := by
  unfold sinAbsTerm factDiv
  let x := ratPow theta (2 * (M + j) + 1)
  let y :=
    ratMul (ratPow theta (2 * M + 1))
      (ratPow (ratMul theta theta) j)
  have xy : RatEq x y := by
    unfold x y
    exact oddPow_split theta M j
  have yNonneg : ratLe ratZero y := by
    unfold y
    exact ratMul_nonneg
      (ratPow_nonneg h0 (2 * M + 1))
      (ratPow_nonneg (ratMul_nonneg h0 h0) j)
  have denLe : ratLe (factDen (2 * M + 1)) (factDen (2 * (M + j) + 1)) := by
    exact factDen_le_of_nat_le (by
      apply Nat.succ_le_succ
      exact Nat.mul_le_mul_left 2 (Nat.le_add_right M j))
  have divLe :
      ratLe
        (ratDivApart y (factDen (2 * (M + j) + 1))
          (factDen_apart (2 * (M + j) + 1)))
        (ratDivApart y (factDen (2 * M + 1))
          (factDen_apart (2 * M + 1))) := by
    exact ratDivApart_le_same_num_den_mono yNonneg
      (factDen_pos (2 * M + 1))
      (factDen_pos (2 * (M + j) + 1))
      (factDen_apart (2 * M + 1))
      (factDen_apart (2 * (M + j) + 1))
      denLe
  have leftEq :
      RatEq
        (ratDivApart x (factDen (2 * (M + j) + 1))
          (factDen_apart (2 * (M + j) + 1)))
        (ratDivApart y (factDen (2 * (M + j) + 1))
          (factDen_apart (2 * (M + j) + 1))) := by
    unfold ratDivApart
    exact ratMul_respects xy (RatEq_refl _)
  have rightEq :
      RatEq
        (ratDivApart y (factDen (2 * M + 1))
          (factDen_apart (2 * M + 1)))
        (ratMul
          (ratDivApart (ratPow theta (2 * M + 1))
            (factDen (2 * M + 1))
            (factDen_apart (2 * M + 1)))
          (ratPow (ratMul theta theta) j)) := by
    unfold y ratDivApart
    exact RatEq_trans _ _ _
      (ratMul_assoc
        (ratPow theta (2 * M + 1))
        (ratPow (ratMul theta theta) j)
        (ratInvApart (factDen (2 * M + 1))
          (factDen_apart (2 * M + 1))))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratPow theta (2 * M + 1)))
          (ratMul_comm
            (ratPow (ratMul theta theta) j)
            (ratInvApart (factDen (2 * M + 1))
              (factDen_apart (2 * M + 1)))))
        (RatEq_symm
          (ratMul_assoc
            (ratPow theta (2 * M + 1))
            (ratInvApart (factDen (2 * M + 1))
              (factDen_apart (2 * M + 1)))
            (ratPow (ratMul theta theta) j))))
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left leftEq divLe)
    rightEq

theorem cosAbsTerm_le_scaled_geom_term
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M j : Nat) :
    ratLe (cosAbsTerm theta (M + j))
      (ratMul
        (factDiv (ratPow theta (2 * M)) (2 * M))
        (ratPow (ratMul theta theta) j)) := by
  unfold cosAbsTerm factDiv
  let x := ratPow theta (2 * (M + j))
  let y :=
    ratMul (ratPow theta (2 * M))
      (ratPow (ratMul theta theta) j)
  have xy : RatEq x y := by
    unfold x y
    exact evenPow_split theta M j
  have yNonneg : ratLe ratZero y := by
    unfold y
    exact ratMul_nonneg
      (ratPow_nonneg h0 (2 * M))
      (ratPow_nonneg (ratMul_nonneg h0 h0) j)
  have denLe : ratLe (factDen (2 * M)) (factDen (2 * (M + j))) := by
    exact factDen_le_of_nat_le
      (Nat.mul_le_mul_left 2 (Nat.le_add_right M j))
  have divLe :
      ratLe
        (ratDivApart y (factDen (2 * (M + j)))
          (factDen_apart (2 * (M + j))))
        (ratDivApart y (factDen (2 * M))
          (factDen_apart (2 * M))) := by
    exact ratDivApart_le_same_num_den_mono yNonneg
      (factDen_pos (2 * M))
      (factDen_pos (2 * (M + j)))
      (factDen_apart (2 * M))
      (factDen_apart (2 * (M + j)))
      denLe
  have leftEq :
      RatEq
        (ratDivApart x (factDen (2 * (M + j)))
          (factDen_apart (2 * (M + j))))
        (ratDivApart y (factDen (2 * (M + j)))
          (factDen_apart (2 * (M + j)))) := by
    unfold ratDivApart
    exact ratMul_respects xy (RatEq_refl _)
  have rightEq :
      RatEq
        (ratDivApart y (factDen (2 * M))
          (factDen_apart (2 * M)))
        (ratMul
          (ratDivApart (ratPow theta (2 * M))
            (factDen (2 * M))
            (factDen_apart (2 * M)))
          (ratPow (ratMul theta theta) j)) := by
    unfold y ratDivApart
    exact RatEq_trans _ _ _
      (ratMul_assoc
        (ratPow theta (2 * M))
        (ratPow (ratMul theta theta) j)
        (ratInvApart (factDen (2 * M))
          (factDen_apart (2 * M))))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratPow theta (2 * M)))
          (ratMul_comm
            (ratPow (ratMul theta theta) j)
            (ratInvApart (factDen (2 * M))
              (factDen_apart (2 * M)))))
        (RatEq_symm
          (ratMul_assoc
            (ratPow theta (2 * M))
            (ratInvApart (factDen (2 * M))
              (factDen_apart (2 * M)))
            (ratPow (ratMul theta theta) j))))
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left leftEq divLe)
    rightEq

theorem signedTermFromAbs_upper
    {absTerm : Nat -> Rat}
    (habs : ∀ k : Nat, ratLe ratZero (absTerm k))
    (k : Nat) :
    ratLe (signedTermFromAbs absTerm k) (absTerm k) := by
  unfold signedTermFromAbs
  by_cases h : k % 2 = 0
  · rw [if_pos h]
    exact ratLe_refl (absTerm k)
  · rw [if_neg h]
    exact ratNeg_le_self_of_nonneg (habs k)

theorem signedTermFromAbs_lower
    {absTerm : Nat -> Rat}
    (habs : ∀ k : Nat, ratLe ratZero (absTerm k))
    (k : Nat) :
    ratLe (ratNeg (absTerm k)) (signedTermFromAbs absTerm k) := by
  unfold signedTermFromAbs
  by_cases h : k % 2 = 0
  · rw [if_pos h]
    exact ratNeg_le_self_of_nonneg (habs k)
  · rw [if_neg h]
    exact ratLe_refl (ratNeg (absTerm k))

theorem signedTail_upper_to_positive_tail
    (M K : Nat)
    {absTerm : Nat -> Rat}
    (habs : ∀ k : Nat, ratLe ratZero (absTerm k))
    :
    ratLe
      (ratSum K (fun j => signedTermFromAbs absTerm (M + j)))
      (ratSum K (fun j => absTerm (M + j))) := by
  apply ratSum_le_sum
  intro j hj
  exact signedTermFromAbs_upper habs (M + j)

theorem signedTail_lower_from_positive_tail
    (M K : Nat)
    {absTerm : Nat -> Rat}
    (habs : ∀ k : Nat, ratLe ratZero (absTerm k))
    :
    ratLe
      (ratNeg (ratSum K (fun j => absTerm (M + j))))
      (ratSum K (fun j => signedTermFromAbs absTerm (M + j))) := by
  have hneg :
      RatEq
        (ratNeg (ratSum K (fun j => absTerm (M + j))))
        (ratSum K (fun j => ratNeg (absTerm (M + j)))) :=
    ratSum_neg (fun j => absTerm (M + j)) K
  have hsum :
      ratLe
        (ratSum K (fun j => ratNeg (absTerm (M + j))))
        (ratSum K (fun j => signedTermFromAbs absTerm (M + j))) := by
    apply ratSum_le_sum
    intro j hj
    exact signedTermFromAbs_lower habs (M + j)
  exact ratLe_of_RatEq_left hneg hsum

theorem sinTailSigned_upper
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M K : Nat) :
    ratLe (sinTailSigned theta M K) (sinAbsTail theta M K) := by
  unfold sinTailSigned sinTerm sinAbsTail
  exact signedTail_upper_to_positive_tail
    M K
    (fun k => sinAbsTerm_nonneg h0 k)

theorem sinTailSigned_lower
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M K : Nat) :
    ratLe (ratNeg (sinAbsTail theta M K)) (sinTailSigned theta M K) := by
  unfold sinTailSigned sinTerm sinAbsTail
  exact signedTail_lower_from_positive_tail
    M K
    (fun k => sinAbsTerm_nonneg h0 k)

theorem cosTailSigned_upper
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M K : Nat) :
    ratLe (cosTailSigned theta M K) (cosAbsTail theta M K) := by
  unfold cosTailSigned cosTerm cosAbsTail
  exact signedTail_upper_to_positive_tail
    M K
    (fun k => cosAbsTerm_nonneg h0 k)

theorem cosTailSigned_lower
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (M K : Nat) :
    ratLe (ratNeg (cosAbsTail theta M K)) (cosTailSigned theta M K) := by
  unfold cosTailSigned cosTerm cosAbsTail
  exact signedTail_lower_from_positive_tail
    M K
    (fun k => cosAbsTerm_nonneg h0 k)

theorem sinAbsTail_le_bound
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M K : Nat) :
    ratLe (sinAbsTail theta M K) (sinTailBound theta h0 h1 M) := by
  let q := ratMul theta theta
  let gap := ratSub ratOne q
  let hgap : ratApart0 gap := one_sub_sq_apart theta h0 h1
  let scale := factDiv (ratPow theta (2 * M + 1)) (2 * M + 1)
  have hTailToGeom :
      ratLe (sinAbsTail theta M K)
        (ratMul scale (geomSum q K)) := by
    unfold sinAbsTail geomSum scale q
    have termwise :
        ratLe
          (ratSum K (fun j => sinAbsTerm theta (M + j)))
          (ratSum K
            (fun j =>
              ratMul
                (factDiv (ratPow theta (2 * M + 1)) (2 * M + 1))
                (ratPow (ratMul theta theta) j))) := by
      apply ratSum_le_sum
      intro j _hj
      exact sinAbsTerm_le_scaled_geom_term h0 M j
    have sumEq :
        RatEq
          (ratSum K
            (fun j =>
              ratMul
                (factDiv (ratPow theta (2 * M + 1)) (2 * M + 1))
                (ratPow (ratMul theta theta) j)))
          (ratMul
            (factDiv (ratPow theta (2 * M + 1)) (2 * M + 1))
            (ratSum K (fun j => ratPow (ratMul theta theta) j))) :=
      RatEq_symm
        (ratMul_sum_left
          (factDiv (ratPow theta (2 * M + 1)) (2 * M + 1))
          K
          (fun j => ratPow (ratMul theta theta) j))
    exact ratLe_of_RatEq_right termwise sumEq
  have hA_nonneg : ratLe ratZero (ratPow theta (2 * M + 1)) := by
    exact ratPow_nonneg h0 (2 * M + 1)
  have hScaleNonneg : ratLe ratZero scale := by
    unfold scale factDiv
    exact ratDivApart_nonneg_of_nonneg_pos
      hA_nonneg
      (factDen_pos (2 * M + 1))
      (factDen_apart (2 * M + 1))
  have hqNonneg : ratLe ratZero q := by
    unfold q
    exact ratMul_nonneg h0 h0
  have hqLtOne : ratLt q ratOne := by
    unfold q
    exact sq_lt_one_of_nonneg_lt_one h0 h1
  have hGeom :
      ratLe (geomSum q K) (ratDivApart ratOne gap hgap) := by
    unfold gap hgap
    exact geomSum_le_inv_one_sub q hqNonneg hqLtOne K
      (one_sub_sq_apart theta h0 h1)
  have hScaled :
      ratLe
        (ratMul scale (geomSum q K))
        (ratMul scale (ratDivApart ratOne gap hgap)) :=
    ratMul_le_mul_nonneg_left hGeom hScaleNonneg
  have hCollapse :
      RatEq
        (ratMul scale (ratDivApart ratOne gap hgap))
        (ratDivApart
          (ratPow theta (2 * M + 1))
          (ratMul (factDen (2 * M + 1)) gap)
          (factTailDen_apart theta h0 h1 (2 * M + 1))) := by
    unfold scale factDiv
    exact ratDivApart_scaled_geom_collapse
      (ratPow theta (2 * M + 1))
      (factDen (2 * M + 1))
      gap
      (factDen_apart (2 * M + 1))
      hgap
      (factTailDen_apart theta h0 h1 (2 * M + 1))
  unfold sinTailBound factorialTailBound
  exact ratLe_of_RatEq_right
    (ratLe_trans hTailToGeom hScaled)
    hCollapse

theorem cosAbsTail_le_bound
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M K : Nat) :
    ratLe (cosAbsTail theta M K) (cosTailBound theta h0 h1 M) := by
  let q := ratMul theta theta
  let gap := ratSub ratOne q
  let hgap : ratApart0 gap := one_sub_sq_apart theta h0 h1
  let scale := factDiv (ratPow theta (2 * M)) (2 * M)
  have hTailToGeom :
      ratLe (cosAbsTail theta M K)
        (ratMul scale (geomSum q K)) := by
    unfold cosAbsTail geomSum scale q
    have termwise :
        ratLe
          (ratSum K (fun j => cosAbsTerm theta (M + j)))
          (ratSum K
            (fun j =>
              ratMul
                (factDiv (ratPow theta (2 * M)) (2 * M))
                (ratPow (ratMul theta theta) j))) := by
      apply ratSum_le_sum
      intro j _hj
      exact cosAbsTerm_le_scaled_geom_term h0 M j
    have sumEq :
        RatEq
          (ratSum K
            (fun j =>
              ratMul
                (factDiv (ratPow theta (2 * M)) (2 * M))
                (ratPow (ratMul theta theta) j)))
          (ratMul
            (factDiv (ratPow theta (2 * M)) (2 * M))
            (ratSum K (fun j => ratPow (ratMul theta theta) j))) :=
      RatEq_symm
        (ratMul_sum_left
          (factDiv (ratPow theta (2 * M)) (2 * M))
          K
          (fun j => ratPow (ratMul theta theta) j))
    exact ratLe_of_RatEq_right termwise sumEq
  have hA_nonneg : ratLe ratZero (ratPow theta (2 * M)) := by
    exact ratPow_nonneg h0 (2 * M)
  have hScaleNonneg : ratLe ratZero scale := by
    unfold scale factDiv
    exact ratDivApart_nonneg_of_nonneg_pos
      hA_nonneg
      (factDen_pos (2 * M))
      (factDen_apart (2 * M))
  have hqNonneg : ratLe ratZero q := by
    unfold q
    exact ratMul_nonneg h0 h0
  have hqLtOne : ratLt q ratOne := by
    unfold q
    exact sq_lt_one_of_nonneg_lt_one h0 h1
  have hGeom :
      ratLe (geomSum q K) (ratDivApart ratOne gap hgap) := by
    unfold gap hgap
    exact geomSum_le_inv_one_sub q hqNonneg hqLtOne K
      (one_sub_sq_apart theta h0 h1)
  have hScaled :
      ratLe
        (ratMul scale (geomSum q K))
        (ratMul scale (ratDivApart ratOne gap hgap)) :=
    ratMul_le_mul_nonneg_left hGeom hScaleNonneg
  have hCollapse :
      RatEq
        (ratMul scale (ratDivApart ratOne gap hgap))
        (ratDivApart
          (ratPow theta (2 * M))
          (ratMul (factDen (2 * M)) gap)
          (factTailDen_apart theta h0 h1 (2 * M))) := by
    unfold scale factDiv
    exact ratDivApart_scaled_geom_collapse
      (ratPow theta (2 * M))
      (factDen (2 * M))
      gap
      (factDen_apart (2 * M))
      hgap
      (factTailDen_apart theta h0 h1 (2 * M))
  unfold cosTailBound factorialTailBound
  exact ratLe_of_RatEq_right
    (ratLe_trans hTailToGeom hScaled)
    hCollapse

theorem sinTailSigned_bound
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M K : Nat) :
    ratLe
      (ratNeg (sinTailBound theta h0 h1 M))
      (sinTailSigned theta M K) ∧
    ratLe
      (sinTailSigned theta M K)
      (sinTailBound theta h0 h1 M) := by
  have upperToAbs :
      ratLe (sinTailSigned theta M K) (sinAbsTail theta M K) :=
    sinTailSigned_upper h0 M K
  have absToBound :
      ratLe (sinAbsTail theta M K) (sinTailBound theta h0 h1 M) :=
    sinAbsTail_le_bound h0 h1 M K
  have lowerAbs :
      ratLe (ratNeg (sinAbsTail theta M K)) (sinTailSigned theta M K) :=
    sinTailSigned_lower h0 M K
  have lowerBound :
      ratLe
        (ratNeg (sinTailBound theta h0 h1 M))
        (ratNeg (sinAbsTail theta M K)) :=
    ratLe_neg_anti absToBound
  exact And.intro
    (ratLe_trans lowerBound lowerAbs)
    (ratLe_trans upperToAbs absToBound)

theorem cosTailSigned_bound
    {theta : Rat}
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne)
    (M K : Nat) :
    ratLe
      (ratNeg (cosTailBound theta h0 h1 M))
      (cosTailSigned theta M K) ∧
    ratLe
      (cosTailSigned theta M K)
      (cosTailBound theta h0 h1 M) := by
  have upperToAbs :
      ratLe (cosTailSigned theta M K) (cosAbsTail theta M K) :=
    cosTailSigned_upper h0 M K
  have absToBound :
      ratLe (cosAbsTail theta M K) (cosTailBound theta h0 h1 M) :=
    cosAbsTail_le_bound h0 h1 M K
  have lowerAbs :
      ratLe (ratNeg (cosAbsTail theta M K)) (cosTailSigned theta M K) :=
    cosTailSigned_lower h0 M K
  have lowerBound :
      ratLe
        (ratNeg (cosTailBound theta h0 h1 M))
        (ratNeg (cosAbsTail theta M K)) :=
    ratLe_neg_anti absToBound
  exact And.intro
    (ratLe_trans lowerBound lowerAbs)
    (ratLe_trans upperToAbs absToBound)

theorem sinPart_add_tail (theta : Rat) (M K : Nat) :
    RatEq (sinPart theta (M + K))
      (ratAdd (sinPart theta M) (sinTailSigned theta M K)) := by
  induction K with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (sinPart theta M)
        (ratAdd (sinPart theta M) ratZero)
      exact RatEq_symm (ratAdd_zero_right (sinPart theta M))
  | succ K ih =>
      rw [Nat.add_succ]
      change RatEq
        (ratAdd (ratSum (M + K) (sinTerm theta))
          (sinTerm theta (M + K)))
        (ratAdd (sinPart theta M)
          (ratAdd (sinTailSigned theta M K)
            (sinTerm theta (M + K))))
      have regroup :
          RatEq
            (ratAdd
              (ratAdd (sinPart theta M) (sinTailSigned theta M K))
              (sinTerm theta (M + K)))
            (ratAdd (sinPart theta M)
              (ratAdd (sinTailSigned theta M K)
                (sinTerm theta (M + K)))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (sinPart theta M)
          (sinTailSigned theta M K)
          (sinTerm theta (M + K))
      exact RatEq_trans _ _ _
        (ratAdd_respects ih (RatEq_refl (sinTerm theta (M + K))))
        regroup

theorem cosPart_add_tail (theta : Rat) (M K : Nat) :
    RatEq (cosPart theta (M + K))
      (ratAdd (cosPart theta M) (cosTailSigned theta M K)) := by
  induction K with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (cosPart theta M)
        (ratAdd (cosPart theta M) ratZero)
      exact RatEq_symm (ratAdd_zero_right (cosPart theta M))
  | succ K ih =>
      rw [Nat.add_succ]
      change RatEq
        (ratAdd (ratSum (M + K) (cosTerm theta))
          (cosTerm theta (M + K)))
        (ratAdd (cosPart theta M)
          (ratAdd (cosTailSigned theta M K)
            (cosTerm theta (M + K))))
      have regroup :
          RatEq
            (ratAdd
              (ratAdd (cosPart theta M) (cosTailSigned theta M K))
              (cosTerm theta (M + K)))
            (ratAdd (cosPart theta M)
              (ratAdd (cosTailSigned theta M K)
                (cosTerm theta (M + K)))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (cosPart theta M)
          (cosTailSigned theta M K)
          (cosTerm theta (M + K))
      exact RatEq_trans _ _ _
        (ratAdd_respects ih (RatEq_refl (cosTerm theta (M + K))))
        regroup

theorem sin_full_enclosure_rat
    (theta : Rat)
    (M : Nat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne) :
    RatNumTrig.SeriesEnclosedFrom
      (sinTerm theta)
      M
      (sinLo theta h0 h1 M)
      (sinHi theta h0 h1 M) := by
  intro K
  have hsplit :
      RatEq (sinPart theta (M + K))
        (ratAdd (sinPart theta M) (sinTailSigned theta M K)) :=
    sinPart_add_tail theta M K
  have htail :=
    sinTailSigned_bound h0 h1 M K
  have hlo :
      ratLe
        (sinLo theta h0 h1 M)
        (ratAdd (sinPart theta M) (sinTailSigned theta M K)) := by
    unfold sinLo ratSub
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (sinPart theta M))
      htail.left
  have hhi :
      ratLe
        (ratAdd (sinPart theta M) (sinTailSigned theta M K))
        (sinHi theta h0 h1 M) := by
    unfold sinHi
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (sinPart theta M))
      htail.right
  exact And.intro
    (ratLe_of_RatEq_right hlo (RatEq_symm hsplit))
    (ratLe_of_RatEq_left hsplit hhi)

theorem cos_full_enclosure_rat
    (theta : Rat)
    (M : Nat)
    (h0 : ratLe ratZero theta)
    (h1 : ratLt theta ratOne) :
    RatNumTrig.SeriesEnclosedFrom
      (cosTerm theta)
      M
      (cosLo theta h0 h1 M)
      (cosHi theta h0 h1 M) := by
  intro K
  have hsplit :
      RatEq (cosPart theta (M + K))
        (ratAdd (cosPart theta M) (cosTailSigned theta M K)) :=
    cosPart_add_tail theta M K
  have htail :=
    cosTailSigned_bound h0 h1 M K
  have hlo :
      ratLe
        (cosLo theta h0 h1 M)
        (ratAdd (cosPart theta M) (cosTailSigned theta M K)) := by
    unfold cosLo ratSub
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (cosPart theta M))
      htail.left
  have hhi :
      ratLe
        (ratAdd (cosPart theta M) (cosTailSigned theta M K))
        (cosHi theta h0 h1 M) := by
    unfold cosHi
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (cosPart theta M))
      htail.right
  exact And.intro
    (ratLe_of_RatEq_right hlo (RatEq_symm hsplit))
    (ratLe_of_RatEq_left hsplit hhi)

end BEDC.Real.RatNumSinCos
