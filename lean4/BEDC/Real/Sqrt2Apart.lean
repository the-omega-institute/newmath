import BEDC.Real.DyadicIntervalStream

namespace BEDC.Real.DyadicIntervalStream

open BEDC.Derived.Sqrt2BisectionUp

private abbrev L (n : Nat) : Rat :=
  DReal.loQ sqrt2D n

private abbrev U (n : Nat) : Rat :=
  DReal.hiQ sqrt2D n

private theorem nat_sub_eq_zero_of_le_clean {a b : Nat} :
    a <= b -> a - b = 0 := by
  intro h
  induction b generalizing a with
  | zero =>
      cases a with
      | zero =>
          rfl
      | succ a =>
          cases h
  | succ b ih =>
      cases a with
      | zero =>
          induction b with
          | zero =>
              rfl
          | succ b _ih =>
              rw [Nat.zero_sub]
      | succ a =>
          rw [Nat.succ_sub_succ_eq_sub]
          exact ih (Nat.le_of_succ_le_succ h)

private theorem int_nat_le_of_nat_le {a b : Nat} :
    a <= b -> (Int.ofNat a : Int) <= Int.ofNat b := by
  intro h
  apply (Int.le_def (a := Int.ofNat a) (b := Int.ofNat b)).mpr
  change ((Int.ofNat b).sub (Int.ofNat a)).NonNeg
  unfold Int.sub
  change (Int.ofNat b + -Int.ofNat a).NonNeg
  cases a with
  | zero =>
      change (Int.ofNat b + Int.ofNat 0).NonNeg
      unfold HAdd.hAdd instHAdd Add.add Int.instAdd Int.add
      exact Int.NonNeg.mk b
  | succ a =>
      change (Int.ofNat b + Int.negSucc a).NonNeg
      unfold HAdd.hAdd instHAdd Add.add Int.instAdd Int.add
      change (Int.subNatNat b (Nat.succ a)).NonNeg
      unfold Int.subNatNat
      rw [nat_sub_eq_zero_of_le_clean h]
      exact Int.NonNeg.mk (b - Nat.succ a)

private theorem int_nat_lt_of_nat_lt {a b : Nat} :
    a < b -> (Int.ofNat a : Int) < Int.ofNat b := by
  intro h
  change (Int.ofNat a : Int) + 1 <= Int.ofNat b
  change Int.ofNat (a + 1) <= Int.ofNat b
  exact int_nat_le_of_nat_le (Nat.succ_le_of_lt h)

private theorem nat_mul_assoc_local (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := by
          rw [ih]
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := by
          rw [Nat.mul_succ b c]

private theorem nat_mul_left_assoc_local (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  rw [← nat_mul_assoc_local a b c]
  rw [← nat_mul_assoc_local b a c]
  rw [Nat.mul_comm a b]

private theorem nat_square_mul_square (a b : Nat) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc
    (a * b) * (a * b) = a * (b * (a * b)) := nat_mul_assoc_local a b (a * b)
    _ = a * (a * (b * b)) := by
      rw [nat_mul_left_assoc_local b a b]
    _ = (a * a) * (b * b) := (nat_mul_assoc_local a a (b * b)).symm

private theorem nat_two_square_mul (d : Nat) :
    2 * d * d = 2 * (d * d) := by
  exact nat_mul_assoc_local 2 d d

private theorem nat_mul_four_comm (a b c d : Nat) :
    ((a * b) * (c * d)) = ((a * c) * (b * d)) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) := nat_mul_assoc_local a b (c * d)
    _ = a * (c * (b * d)) := by
      rw [nat_mul_left_assoc_local b c d]
    _ = (a * c) * (b * d) := (nat_mul_assoc_local a c (b * d)).symm

private theorem nat_two_square_swap (a b : Nat) :
    (2 * (a * a)) * (b * b) = (2 * (b * b)) * (a * a) := by
  calc
    (2 * (a * a)) * (b * b) = (2 * b) * ((a * a) * b) :=
      nat_mul_four_comm 2 (a * a) b b
    _ = (2 * b) * (b * (a * a)) := by
      rw [Nat.mul_comm (a * a) b]
    _ = (2 * b * b) * (a * a) := by
      rw [nat_mul_assoc_local (2 * b) b (a * a)]
    _ = (2 * (b * b)) * (a * a) := by
      rw [nat_mul_assoc_local 2 b b]

private theorem nat_mul_move_last (a b c : Nat) :
    (a * b) * c = (a * c) * b := by
  calc
    (a * b) * c = a * (b * c) := nat_mul_assoc_local a b c
    _ = a * (c * b) := by
      rw [Nat.mul_comm b c]
    _ = (a * c) * b := (nat_mul_assoc_local a c b).symm

private theorem nat_add_four_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_square_succ (a : Nat) :
    (a + 1) * (a + 1) = a * a + (a + a + 1) := by
  calc
    (a + 1) * (a + 1) = (a + 1) * a + (a + 1) := Nat.mul_succ (a + 1) a
    _ = (a * a + 1 * a) + (a + 1) := by
      rw [Nat.add_mul]
    _ = (a * a + a) + (a + 1) := by
      rw [Nat.one_mul]
    _ = (a * a + a) + a + 1 := Nat.add_assoc (a * a + a) a 1
    _ = a * a + (a + a) + 1 := by
      rw [← Nat.add_assoc (a * a) a a]
    _ = a * a + (a + a + 1) := (Nat.add_assoc (a * a) (a + a) 1).symm

private theorem nat_four_eq_two_mul_two :
    4 = 2 * 2 := by
  rfl

private theorem nat_pow_two_clean (n : Nat) :
    n ^ 2 = n * n := by
  rw [show 2 = Nat.succ 1 by rfl]
  rw [Nat.pow_succ]
  rw [show 1 = Nat.succ 0 by rfl]
  rw [Nat.pow_succ]
  rw [Nat.pow_zero]
  rw [Nat.one_mul]

private theorem pos_den_succ (d : Nat) : 0 < Nat.succ d :=
  Nat.succ_pos d

private theorem powTwoNat_self_covers (threshold : Nat) :
    threshold <= powTwoNat threshold := by
  induction threshold with
  | zero =>
      exact Nat.zero_le _
  | succ threshold ih =>
      change Nat.succ threshold <= 2 * powTwoNat threshold
      have stepToPow :
          Nat.succ threshold <= Nat.succ (powTwoNat threshold) :=
        Nat.succ_le_succ ih
      have powStep :
          Nat.succ (powTwoNat threshold) <= 2 * powTwoNat threshold := by
        rw [Nat.two_mul]
        change powTwoNat threshold + 1 <=
          powTwoNat threshold + powTwoNat threshold
        exact Nat.add_le_add_left
          (powTwoNat_pos threshold) (powTwoNat threshold)
      exact Nat.le_trans stepToPow powStep

private theorem nat_lt_powTwoNat_succ_self (n : Nat) :
    n < powTwoNat (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (powTwoNat_self_covers (n + 1))

private theorem nat_sub_add_cancel_clean {a b : Nat} :
    b <= a -> a - b + b = a := by
  intro h
  induction b generalizing a with
  | zero =>
      rw [Nat.sub_zero, Nat.add_zero]
  | succ b ih =>
      cases a with
      | zero =>
          cases h
      | succ a =>
          rw [Nat.succ_sub_succ_eq_sub]
          have hb : b <= a := Nat.le_of_succ_le_succ h
          have ih' := ih hb
          calc
            a - b + Nat.succ b = Nat.succ (a - b + b) := by
              rw [Nat.add_succ]
            _ = Nat.succ a := by
              rw [ih']

private theorem nat_sub_lt_sub_right_clean {a b c : Nat} :
    c <= a -> a < b -> a - c < b - c := by
  intro hca hab
  have hcb : c <= b := Nat.le_trans hca (Nat.le_of_lt hab)
  have leftEq := nat_sub_add_cancel_clean hca
  have rightEq := nat_sub_add_cancel_clean hcb
  have hAdd : (a - c) + c < (b - c) + c := by
    rw [leftEq, rightEq]
    exact hab
  exact Nat.lt_of_add_lt_add_right hAdd

private theorem nat_sq_lt_sq_of_lt {a b : Nat} (h : a < b) :
    a * a < b * b := by
  have hbpos : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) h
  cases a with
  | zero =>
      change 0 < b * b
      exact Nat.mul_pos hbpos hbpos
  | succ a =>
      have hpos : 0 < Nat.succ a := Nat.succ_pos a
      have h1 :
          Nat.succ a * Nat.succ a < b * Nat.succ a :=
        Nat.mul_lt_mul_of_pos_right h hpos
      have h2 :
          b * Nat.succ a < b * b :=
        Nat.mul_lt_mul_of_pos_left h hbpos
      exact Nat.lt_trans h1 h2

private theorem nat_lt_of_sq_lt_sq {a b : Nat} (h : a * a < b * b) :
    a < b := by
  match Nat.lt_or_ge a b with
  | Or.inl hab =>
      exact hab
  | Or.inr hba =>
      have hs : b * b <= a * a := by
        match Nat.lt_or_eq_of_le hba with
        | Or.inr heq =>
            rw [heq]
            exact Nat.le_refl _
        | Or.inl hlt =>
            exact Nat.le_of_lt (nat_sq_lt_sq_of_lt hlt)
      exact False.elim ((Nat.not_lt_of_ge hs) h)

private theorem rat_lt_pos_num_iff_nat_lt
    {a b da db : Nat} (hda : 0 < da) (hdb : 0 < db) :
    Rat.lt { num := Int.ofNat a, den := da, den_pos := hda }
      { num := Int.ofNat b, den := db, den_pos := hdb } ->
    a * db < b * da := by
  intro h
  change (Int.ofNat a * Int.ofNat db) < (Int.ofNat b * Int.ofNat da) at h
  change (Int.ofNat (a * db) : Int) < Int.ofNat (b * da) at h
  exact (Int.ofNat_lt.mp h)

private theorem rat_lt_of_nat_cross
    {a b da db : Nat} (hda : 0 < da) (hdb : 0 < db)
    (h : a * db < b * da) :
    Rat.lt { num := Int.ofNat a, den := da, den_pos := hda }
      { num := Int.ofNat b, den := db, den_pos := hdb } := by
  unfold Rat.lt
  change (Int.ofNat a * Int.ofNat db) < (Int.ofNat b * Int.ofNat da)
  change (Int.ofNat (a * db) : Int) < Int.ofNat (b * da)
  exact int_nat_lt_of_nat_lt h

private theorem rat_le_of_nat_cross
    {a b da db : Nat} (hda : 0 < da) (hdb : 0 < db)
    (h : a * db <= b * da) :
    Rat.le { num := Int.ofNat a, den := da, den_pos := hda }
      { num := Int.ofNat b, den := db, den_pos := hdb } := by
  unfold Rat.le
  change (Int.ofNat a * Int.ofNat db) <= (Int.ofNat b * Int.ofNat da)
  change (Int.ofNat (a * db) : Int) <= Int.ofNat (b * da)
  exact int_nat_le_of_nat_le h

private theorem rat_lt_lower_two_of_le_one
    {p d : Nat} (hd : 0 < d) (hp : p <= d) :
    Rat.lt { num := Int.ofNat p, den := d, den_pos := hd } (L 2) := by
  unfold L DReal.loQ Rat.ofIntOverPowTwo sqrt2D sqrt2LoInt sqrt2LoNat
  apply rat_lt_of_nat_cross hd (by decide : 0 < 4)
  have h1 : p * 4 <= d * 4 := Nat.mul_le_mul_right 4 hp
  have h2 : d * 4 < d * 5 :=
    Nat.mul_lt_mul_of_pos_left (by decide : 4 < 5) hd
  calc
    p * 4 <= d * 4 := h1
    _ < d * 5 := h2
    _ = 5 * d := Nat.mul_comm d 5

private theorem rat_upper_one_lt_of_two_le
    {p d : Nat} (hd : 0 < d) (hp : 2 * d <= p) :
    Rat.lt (U 1) { num := Int.ofNat p, den := d, den_pos := hd } := by
  unfold U DReal.hiQ Rat.ofIntOverPowTwo sqrt2D sqrt2HiInt sqrt2HiNat
  apply rat_lt_of_nat_cross (by decide : 0 < 2) hd
  have htwice : 2 * (2 * d) <= 2 * p := Nat.mul_le_mul_left 2 hp
  have hfour : 4 * d = 2 * (2 * d) := by
    calc
      4 * d = (2 * 2) * d := rfl
      _ = 2 * (2 * d) := nat_mul_assoc_local 2 2 d
  have h2 : 3 * d < 4 * d :=
    Nat.mul_lt_mul_of_pos_right (by decide : 3 < 4) hd
  calc
    3 * d < 4 * d := h2
    _ = 2 * (2 * d) := hfour
    _ <= 2 * p := htwice
    _ = p * 2 := Nat.mul_comm 2 p

theorem apart_small_nat
    {p d : Nat} (hd : 0 < d) (hp : p <= d) :
    DReal.ApartRat sqrt2D { num := Int.ofNat p, den := d, den_pos := hd } := by
  exact ⟨2, Or.inl (rat_lt_lower_two_of_le_one hd hp)⟩

theorem apart_large_nat
    {p d : Nat} (hd : 0 < d) (hp : 2 * d <= p) :
    DReal.ApartRat sqrt2D { num := Int.ofNat p, den := d, den_pos := hd } := by
  exact ⟨1, Or.inr (rat_upper_one_lt_of_two_le hd hp)⟩

private theorem sqrt2_bracket_nat (n : Nat) :
    sqrt2LoNat n * sqrt2LoNat n < 2 * (powTwoNat n * powTwoNat n) ∧
      2 * (powTwoNat n * powTwoNat n) < sqrt2HiNat n * sqrt2HiNat n := by
  have h := sqrt2_bracket n
  unfold sqrt2D sqrt2LoInt sqrt2HiInt at h
  change
    sqrt2LoNat n ^ 2 < 2 * powTwoNat n * powTwoNat n /\
      2 * powTwoNat n * powTwoNat n < sqrt2HiNat n ^ 2 at h
  rw [nat_pow_two_clean (sqrt2LoNat n), nat_pow_two_clean (sqrt2HiNat n)] at h
  constructor
  · exact Nat.lt_of_lt_of_le h.left (Nat.le_of_eq (nat_two_square_mul (powTwoNat n)))
  · exact Nat.lt_of_le_of_lt (Nat.le_of_eq (nat_two_square_mul (powTwoNat n)).symm) h.right

private theorem lower_square_lt_two (n : Nat) :
    (sqrt2LoNat n * sqrt2LoNat n) < 2 * (powTwoNat n * powTwoNat n) :=
  (sqrt2_bracket_nat n).left

private theorem two_lt_upper_square (n : Nat) :
    2 * (powTwoNat n * powTwoNat n) < sqrt2HiNat n * sqrt2HiNat n :=
  (sqrt2_bracket_nat n).right

private theorem rat_lt_of_pos_sq_cross
    {a b da db : Nat} (hda : 0 < da) (hdb : 0 < db)
    (h : (a * db) * (a * db) < (b * da) * (b * da)) :
    Rat.lt { num := Int.ofNat a, den := da, den_pos := hda }
      { num := Int.ofNat b, den := db, den_pos := hdb } := by
  exact rat_lt_of_nat_cross hda hdb (nat_lt_of_sq_lt_sq h)

private theorem lower_rat_above_of_sq
    {p d n : Nat} (hd : 0 < d)
    (h : 2 * (d * d) < p * p) :
    Rat.lt (L n) { num := Int.ofNat p, den := d, den_pos := hd } := by
  unfold L DReal.loQ Rat.ofIntOverPowTwo sqrt2D sqrt2LoInt sqrt2LoNat
  apply rat_lt_of_pos_sq_cross (powTwoNat_pos n) hd
  have hbr := lower_square_lt_two n
  have hscale :
      (sqrt2LoNat n * sqrt2LoNat n) * (d * d) <
        (2 * (powTwoNat n * powTwoNat n)) * (d * d) :=
    Nat.mul_lt_mul_of_pos_right hbr (Nat.mul_pos hd hd)
  have hright :
      (2 * (powTwoNat n * powTwoNat n)) * (d * d) <
        (p * p) * (powTwoNat n * powTwoNat n) := by
    calc
      (2 * (powTwoNat n * powTwoNat n)) * (d * d)
          = (2 * (d * d)) * (powTwoNat n * powTwoNat n) := by
            rw [nat_two_square_swap (powTwoNat n) d]
      _ < (p * p) * (powTwoNat n * powTwoNat n) :=
          Nat.mul_lt_mul_of_pos_right h
            (Nat.mul_pos (powTwoNat_pos n) (powTwoNat_pos n))
  have hsq :
      (sqrt2LoNat n * sqrt2LoNat n) * (d * d) <
        (p * p) * (powTwoNat n * powTwoNat n) :=
    Nat.lt_trans hscale hright
  calc
    (sqrt2LoNat n * d) * (sqrt2LoNat n * d)
        = (sqrt2LoNat n * sqrt2LoNat n) * (d * d) :=
          nat_square_mul_square (sqrt2LoNat n) d
    _ < (p * p) * (powTwoNat n * powTwoNat n) := hsq
    _ = (p * powTwoNat n) * (p * powTwoNat n) :=
          (nat_square_mul_square p (powTwoNat n)).symm

private theorem upper_rat_below_of_sq
    {p d n : Nat} (hd : 0 < d)
    (h : p * p < 2 * (d * d)) :
    Rat.lt { num := Int.ofNat p, den := d, den_pos := hd } (U n) := by
  unfold U DReal.hiQ Rat.ofIntOverPowTwo sqrt2D sqrt2HiInt sqrt2HiNat
  apply rat_lt_of_pos_sq_cross hd (powTwoNat_pos n)
  have hleft :
      (p * p) * (powTwoNat n * powTwoNat n) <
        (2 * (d * d)) * (powTwoNat n * powTwoNat n) :=
    Nat.mul_lt_mul_of_pos_right h
      (Nat.mul_pos (powTwoNat_pos n) (powTwoNat_pos n))
  have hright :
      (2 * (d * d)) * (powTwoNat n * powTwoNat n) <
        (sqrt2HiNat n * sqrt2HiNat n) * (d * d) := by
    calc
      (2 * (d * d)) * (powTwoNat n * powTwoNat n)
          = (2 * (powTwoNat n * powTwoNat n)) * (d * d) := by
            rw [nat_two_square_swap d (powTwoNat n)]
      _ < (sqrt2HiNat n * sqrt2HiNat n) * (d * d) :=
          Nat.mul_lt_mul_of_pos_right (two_lt_upper_square n) (Nat.mul_pos hd hd)
  have hsq :
      (p * p) * (powTwoNat n * powTwoNat n) <
        (sqrt2HiNat n * sqrt2HiNat n) * (d * d) :=
    Nat.lt_trans hleft hright
  calc
    (p * powTwoNat n) * (p * powTwoNat n)
        = (p * p) * (powTwoNat n * powTwoNat n) :=
          nat_square_mul_square p (powTwoNat n)
    _ < (sqrt2HiNat n * sqrt2HiNat n) * (d * d) := hsq
    _ = (sqrt2HiNat n * d) * (sqrt2HiNat n * d) :=
          (nat_square_mul_square (sqrt2HiNat n) d).symm

end BEDC.Real.DyadicIntervalStream
