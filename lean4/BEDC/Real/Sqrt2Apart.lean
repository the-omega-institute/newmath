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

private theorem nat_add_mul_local (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c]
  rw [Nat.mul_add]
  rw [Nat.mul_comm c a]
  rw [Nat.mul_comm c b]

private theorem nat_mul_one_local (n : Nat) :
    n * 1 = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change n * 1 + 1 = Nat.succ n
      rw [ih]

private theorem nat_square_succ (a : Nat) :
    (a + 1) * (a + 1) = a * a + (a + a + 1) := by
  calc
    (a + 1) * (a + 1) = (a + 1) * a + (a + 1) := Nat.mul_succ (a + 1) a
    _ = (a * a + 1 * a) + (a + 1) := by
      rw [nat_add_mul_local]
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

private def natEvenLocal : Nat -> Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (Nat.succ n) => natEvenLocal n

private theorem natEvenLocal_double : ∀ n : Nat, natEvenLocal (n + n) = true := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEvenLocal (Nat.succ (Nat.succ (n + n))) = true
      exact ih

private theorem natEvenLocal_succ_double : ∀ n : Nat,
    natEvenLocal (Nat.succ (n + n)) = false := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEvenLocal (Nat.succ (Nat.succ (Nat.succ (n + n)))) = false
      exact ih

private theorem not_double_eq_succ_double_local {a b : Nat} :
    a + a = Nat.succ (b + b) -> False := by
  intro h
  have parity := congrArg natEvenLocal h
  rw [natEvenLocal_double a, natEvenLocal_succ_double b] at parity
  cases parity

private theorem even_or_odd_decomposition (a : Nat) :
    (exists c : Nat, a = c + c) ∨ (exists c : Nat, a = c + c + 1) := by
  induction a with
  | zero =>
      exact Or.inl ⟨0, rfl⟩
  | succ a ih =>
      cases ih with
      | inl evenA =>
          cases evenA with
          | intro c hc =>
              exact Or.inr ⟨c, by rw [hc]⟩
      | inr oddA =>
          cases oddA with
          | intro c hc =>
              exact Or.inl ⟨c + 1, by
                rw [hc]
                change Nat.succ (c + c + 1) = c + 1 + (c + 1)
                rw [Nat.succ_eq_add_one]
                calc
                  c + c + 1 + 1 = c + (c + 1) + 1 := by
                    rw [Nat.add_assoc c c 1]
                  _ = c + 1 + (c + 1) := by
                    rw [Nat.add_assoc c 1 (c + 1)]
                    rw [Nat.add_comm 1 (c + 1)]
                    rw [← Nat.add_assoc c (c + 1) 1]⟩

private theorem odd_square_succ_local (a : Nat) :
    (a + a + 1) * (a + a + 1) =
      Nat.succ (((a + a + 1) * a + a) + ((a + a + 1) * a + a)) := by
  let m := a + a + 1
  have hm : m = a + a + 1 := rfl
  have rearr :
      (m * a + m * a) + (a + a) =
        (m * a + a) + (m * a + a) :=
    nat_add_four_swap (m * a) (m * a) a a
  calc
    (a + a + 1) * (a + a + 1) = m * (a + a + 1) := by
      rw [hm]
    _ = m * ((a + a) + 1) := rfl
    _ = m * (a + a) + m * 1 := Nat.mul_add m (a + a) 1
    _ = m * (a + a) + m := by
      rw [Nat.mul_one]
    _ = (m * a + m * a) + m := by
      rw [Nat.mul_add]
    _ = (m * a + m * a) + (a + a + 1) := by
      rw [hm]
    _ = (m * a + m * a) + ((a + a) + 1) := rfl
    _ = Nat.succ ((m * a + m * a) + (a + a)) := by
      rw [Nat.add_succ]
    _ = Nat.succ ((m * a + a) + (m * a + a)) := by
      rw [rearr]
    _ = Nat.succ (((a + a + 1) * a + a) + ((a + a + 1) * a + a)) := by
      rw [hm]

private theorem odd_square_ne_double_local (n a : Nat) :
    (n + n + 1) * (n + n + 1) = a + a -> False := by
  intro h
  have odd := odd_square_succ_local n
  exact not_double_eq_succ_double_local
    (a := a) (b := ((n + n + 1) * n + n))
    (h.symm.trans odd)

private theorem even_square_halves {a b : Nat} :
    a * a = 2 * b -> exists c : Nat, a = c + c := by
  intro h
  cases even_or_odd_decomposition a with
  | inl evenA =>
      exact evenA
  | inr oddA =>
      cases oddA with
      | intro c hc =>
          rw [hc] at h
          exact False.elim
            (odd_square_ne_double_local c b (by
              rw [h]
              exact Nat.two_mul b))

private theorem double_square_eq (c : Nat) :
    (c + c) * (c + c) = 2 * (2 * (c * c)) := by
  rw [← Nat.two_mul c]
  calc
    (2 * c) * (2 * c) = 2 * (c * (2 * c)) := by
      rw [nat_mul_assoc_local]
    _ = 2 * ((2 * c) * c) := by
      rw [Nat.mul_comm c (2 * c)]
    _ = 2 * (2 * (c * c)) := by
      rw [nat_mul_assoc_local]

private theorem nat_add_sub_cancel_left_local (a b : Nat) :
    a + b - a = b := by
  induction a with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ a ih =>
      rw [Nat.succ_add]
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem succ_double_shape (a : Nat) :
    a + 1 + (a + 1) = Nat.succ (Nat.succ (a + a)) := by
  rw [Nat.add_one]
  rw [Nat.succ_add]
  rw [Nat.add_succ]

private theorem nat_two_mul_cancel_local {a b : Nat} :
    2 * a = 2 * b -> a = b := by
  intro h
  rw [Nat.two_mul] at h
  rw [Nat.two_mul] at h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          rw [Nat.zero_add] at h
          rw [succ_double_shape b] at h
          cases h
  | succ a ih =>
      cases b with
      | zero =>
          rw [Nat.zero_add] at h
          rw [succ_double_shape a] at h
          cases h
      | succ b =>
          rw [succ_double_shape a, succ_double_shape b] at h
          have h3 : a + a = b + b :=
            Nat.succ.inj (Nat.succ.inj h)
          exact congrArg Nat.succ (ih h3)

private theorem nat_not_square_eq_two_square_pos (p d : Nat) :
    0 < p -> p * p = 2 * (d * d) -> False := by
  revert d
  refine Nat.strongRecOn p ?_
  intro p ih d pPos h
  cases even_square_halves h with
  | intro c hp =>
      rw [hp] at h
      have twoEq :
          2 * (2 * (c * c)) = 2 * (d * d) := by
        rw [← double_square_eq c]
        exact h
      have innerEq : 2 * (c * c) = d * d :=
        nat_two_mul_cancel_local twoEq
      have dEven : exists e : Nat, d = e + e :=
        even_square_halves innerEq.symm
      cases dEven with
      | intro e hd =>
          rw [hd] at innerEq
          have fourEq : 2 * (c * c) = 2 * (2 * (e * e)) := by
            rw [← double_square_eq e]
            exact innerEq
          have ccEq : c * c = 2 * (e * e) :=
            nat_two_mul_cancel_local fourEq
          have cPos : 0 < c := by
            cases c with
            | zero =>
                have pZero : p = 0 := by
                  rw [hp]
                rw [pZero] at pPos
                cases pPos
            | succ c =>
                exact Nat.succ_pos c
          have cLtP : c < p := by
            rw [hp]
            exact Nat.lt_add_of_pos_right cPos
          exact ih c cLtP e cPos ccEq

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

private theorem nat_le_add_of_sub_le_local {a b c : Nat} :
    a - b <= c -> a <= c + b := by
  intro h
  cases Nat.lt_or_ge a b with
  | inl altb =>
      exact Nat.le_trans (Nat.le_of_lt altb) (Nat.le_add_left b c)
  | inr bLeA =>
      have shifted : a - b + b <= c + b :=
        Nat.add_le_add_right h b
      rw [nat_sub_add_cancel_clean bLeA] at shifted
      exact shifted

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

private theorem nat_sub_le_sub_left_clean {a b c : Nat} :
    a <= b -> c - b <= c - a := by
  intro h
  induction c generalizing a b with
  | zero =>
      rw [Nat.zero_sub b, Nat.zero_sub a]
      exact Nat.zero_le 0
  | succ c ih =>
      cases a with
      | zero =>
          rw [Nat.sub_zero]
          exact Nat.sub_le (Nat.succ c) b
      | succ a =>
          cases b with
          | zero =>
              cases h
          | succ b =>
              rw [Nat.succ_sub_succ_eq_sub]
              rw [Nat.succ_sub_succ_eq_sub]
              exact ih (Nat.le_of_succ_le_succ h)

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

private theorem sqrt2_hi_le_two_pow_succ (n : Nat) :
    sqrt2HiNat n <= 2 * powTwoNat n := by
  induction n with
  | zero =>
      unfold sqrt2HiNat sqrt2BisectRaw sqrt2BisectInitial powTwoNat
      decide
  | succ n ih =>
      have step := sqrt2HiNat_mono_doubled n
      have scaled : 2 * sqrt2HiNat n <= 2 * (2 * powTwoNat n) :=
        Nat.mul_le_mul_left 2 ih
      exact Nat.le_trans step scaled

private theorem sqrt2_lo_le_two_pow_succ (n : Nat) :
    sqrt2LoNat n <= 2 * powTwoNat n := by
  have hiBound := sqrt2_hi_le_two_pow_succ n
  have loLeHi : sqrt2LoNat n <= sqrt2HiNat n := by
    rw [sqrt2_nat_adjacent n]
    exact Nat.le_succ _
  exact Nat.le_trans loLeHi hiBound

private theorem adjacent_square_gap_le_four_pow (a P : Nat) :
    a + 1 <= 2 * P -> (a + 1) * (a + 1) - a * a <= 4 * P := by
  intro ha
  rw [nat_square_succ a]
  have diffEq : a * a + (a + a + 1) - a * a = a + a + 1 := by
    exact nat_add_sub_cancel_left_local (a * a) (a + a + 1)
  rw [diffEq]
  have aLe : a <= 2 * P := Nat.le_trans (Nat.le_succ a) ha
  have pairLe : a + (a + 1) <= (2 * P) + (2 * P) :=
    Nat.add_le_add aLe ha
  have shape : a + a + 1 = a + (a + 1) := by
    rw [Nat.add_assoc]
  rw [shape]
  exact Nat.le_trans pairLe (Nat.le_of_eq (by
    rw [← Nat.two_mul (2 * P)]
    calc
      2 * (2 * P) = (2 * 2) * P := (nat_mul_assoc_local 2 2 P).symm
      _ = 4 * P := rfl))

private theorem sqrt2_adjacent_square_gap_le_four_pow (n : Nat) :
    sqrt2HiNat n * sqrt2HiNat n - sqrt2LoNat n * sqrt2LoNat n <=
      4 * powTwoNat n := by
  rw [sqrt2_nat_adjacent n]
  exact adjacent_square_gap_le_four_pow (sqrt2LoNat n) (powTwoNat n) (by
    rw [← sqrt2_nat_adjacent n]
    exact sqrt2_hi_le_two_pow_succ n)

private theorem lower_defect_le_four_pow_nat (n : Nat) :
    2 * (powTwoNat n * powTwoNat n) -
        sqrt2LoNat n * sqrt2LoNat n <= 4 * powTwoNat n := by
  have hiLe :
      2 * (powTwoNat n * powTwoNat n) <=
        sqrt2HiNat n * sqrt2HiNat n :=
    Nat.le_of_lt (two_lt_upper_square n)
  exact Nat.le_trans
    (Nat.sub_le_sub_right hiLe (sqrt2LoNat n * sqrt2LoNat n))
    (sqrt2_adjacent_square_gap_le_four_pow n)

private theorem upper_excess_le_four_pow_nat (n : Nat) :
    sqrt2HiNat n * sqrt2HiNat n -
        2 * (powTwoNat n * powTwoNat n) <= 4 * powTwoNat n := by
  have loLe :
      sqrt2LoNat n * sqrt2LoNat n <=
        2 * (powTwoNat n * powTwoNat n) :=
    Nat.le_of_lt (lower_square_lt_two n)
  exact Nat.le_trans
    (nat_sub_le_sub_left_clean loLe)
    (sqrt2_adjacent_square_gap_le_four_pow n)

private theorem four_mul_square_swap (P d : Nat) :
    (4 * P) * (d * d) = (4 * (d * d)) * P := by
  calc
    (4 * P) * (d * d) = 4 * (P * (d * d)) := by
      rw [nat_mul_assoc_local]
    _ = 4 * ((d * d) * P) := by
      rw [Nat.mul_comm P (d * d)]
    _ = (4 * (d * d)) * P := by
      rw [← nat_mul_assoc_local]

private theorem lower_cross_of_gap {p d L P : Nat} :
    4 * (d * d) < P ->
      p * p < 2 * (d * d) ->
        2 * (P * P) - L * L <= 4 * P ->
          p * p * (P * P) < L * L * (d * d) := by
  intro hgap hsq hdef
  have p2Step : p * p + 1 <= 2 * (d * d) :=
    Nat.succ_le_of_lt hsq
  have p2P :
      p * p * (P * P) + P * P <=
        (2 * (d * d)) * (P * P) := by
    calc
      p * p * (P * P) + P * P =
          (p * p + 1) * (P * P) := by
            rw [nat_add_mul_local]
            rw [Nat.one_mul]
      _ <= (2 * (d * d)) * (P * P) :=
          Nat.mul_le_mul_right (P * P) p2Step
  have defectAdd : 2 * (P * P) <= 4 * P + L * L :=
    nat_le_add_of_sub_le_local hdef
  have p2P_to_L :
      p * p * (P * P) + P * P <=
        (4 * P) * (d * d) + L * L * (d * d) := by
    calc
      p * p * (P * P) + P * P
          <= (2 * (d * d)) * (P * P) := p2P
      _ = (2 * (P * P)) * (d * d) := nat_two_square_swap d P
      _ <= (4 * P + L * L) * (d * d) :=
          Nat.mul_le_mul_right (d * d) defectAdd
      _ = (4 * P) * (d * d) + L * L * (d * d) := by
          rw [nat_add_mul_local]
  have Ppos : 0 < P :=
    Nat.lt_of_le_of_lt (Nat.zero_le (4 * (d * d))) hgap
  have gapScaled :
      (4 * P) * (d * d) < P * P := by
    calc
      (4 * P) * (d * d) = (4 * (d * d)) * P :=
        four_mul_square_swap P d
      _ < P * P := Nat.mul_lt_mul_of_pos_right hgap Ppos
  have added :
      p * p * (P * P) + (4 * P) * (d * d) <
        (4 * P) * (d * d) + L * L * (d * d) := by
    exact Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left gapScaled (p * p * (P * P)))
      p2P_to_L
  have reordered :
      (4 * P) * (d * d) + p * p * (P * P) <
        (4 * P) * (d * d) + L * L * (d * d) := by
    calc
      (4 * P) * (d * d) + p * p * (P * P)
          = p * p * (P * P) + (4 * P) * (d * d) :=
            Nat.add_comm ((4 * P) * (d * d)) (p * p * (P * P))
      _ < (4 * P) * (d * d) + L * L * (d * d) := added
  exact Nat.lt_of_add_lt_add_left reordered

private theorem upper_cross_of_gap {p d U P : Nat} :
    4 * (d * d) < P ->
      2 * (d * d) < p * p ->
        U * U - 2 * (P * P) <= 4 * P ->
          U * U * (d * d) < p * p * (P * P) := by
  intro hgap hsq hexcess
  have excessAdd : U * U <= 4 * P + 2 * (P * P) :=
    nat_le_add_of_sub_le_local hexcess
  have Ubound :
      U * U * (d * d) <=
        (4 * P) * (d * d) + (2 * (P * P)) * (d * d) := by
    calc
      U * U * (d * d) <= (4 * P + 2 * (P * P)) * (d * d) :=
        Nat.mul_le_mul_right (d * d) excessAdd
      _ = (4 * P) * (d * d) + (2 * (P * P)) * (d * d) := by
        rw [nat_add_mul_local]
  have p2Step : 2 * (d * d) + 1 <= p * p :=
    Nat.succ_le_of_lt hsq
  have pLower :
      (2 * (P * P)) * (d * d) + P * P <=
        p * p * (P * P) := by
    calc
      (2 * (P * P)) * (d * d) + P * P
          = (2 * (d * d)) * (P * P) + P * P := by
            rw [nat_two_square_swap d P]
      _ = (2 * (d * d) + 1) * (P * P) := by
            rw [nat_add_mul_local]
            rw [Nat.one_mul]
      _ <= p * p * (P * P) :=
            Nat.mul_le_mul_right (P * P) p2Step
  have Ppos : 0 < P :=
    Nat.lt_of_le_of_lt (Nat.zero_le (4 * (d * d))) hgap
  have gapScaled :
      (4 * P) * (d * d) < P * P := by
    calc
      (4 * P) * (d * d) = (4 * (d * d)) * P :=
        four_mul_square_swap P d
      _ < P * P := Nat.mul_lt_mul_of_pos_right hgap Ppos
  have sumLt :
      (4 * P) * (d * d) + (2 * (P * P)) * (d * d) <
        P * P + (2 * (P * P)) * (d * d) :=
    Nat.add_lt_add_right gapScaled ((2 * (P * P)) * (d * d))
  have reorderedLower :
      P * P + (2 * (P * P)) * (d * d) <=
        p * p * (P * P) := by
    rw [Nat.add_comm (P * P) ((2 * (P * P)) * (d * d))]
    exact pLower
  exact Nat.lt_of_le_of_lt Ubound
    (Nat.lt_of_lt_of_le sumLt reorderedLower)

private theorem lower_rat_cross_of_gap
    {p d n : Nat} (hd : 0 < d)
    (hgap : 4 * (d * d) < powTwoNat n)
    (hsq : p * p < 2 * (d * d)) :
    Rat.lt { num := Int.ofNat p, den := d, den_pos := hd } (L n) := by
  unfold L DReal.loQ Rat.ofIntOverPowTwo sqrt2D sqrt2LoInt sqrt2LoNat
  apply rat_lt_of_pos_sq_cross hd (powTwoNat_pos n)
  have hcross := lower_cross_of_gap
    (p := p) (d := d) (L := sqrt2LoNat n) (P := powTwoNat n)
    hgap hsq (lower_defect_le_four_pow_nat n)
  calc
    (p * powTwoNat n) * (p * powTwoNat n)
        = (p * p) * (powTwoNat n * powTwoNat n) :=
          nat_square_mul_square p (powTwoNat n)
    _ < (sqrt2LoNat n * sqrt2LoNat n) * (d * d) := hcross
    _ = (sqrt2LoNat n * d) * (sqrt2LoNat n * d) :=
          (nat_square_mul_square (sqrt2LoNat n) d).symm

private theorem upper_rat_cross_of_gap
    {p d n : Nat} (hd : 0 < d)
    (hgap : 4 * (d * d) < powTwoNat n)
    (hsq : 2 * (d * d) < p * p) :
    Rat.lt (U n) { num := Int.ofNat p, den := d, den_pos := hd } := by
  unfold U DReal.hiQ Rat.ofIntOverPowTwo sqrt2D sqrt2HiInt sqrt2HiNat
  apply rat_lt_of_pos_sq_cross (powTwoNat_pos n) hd
  have hcross := upper_cross_of_gap
    (p := p) (d := d) (U := sqrt2HiNat n) (P := powTwoNat n)
    hgap hsq (upper_excess_le_four_pow_nat n)
  calc
    (sqrt2HiNat n * d) * (sqrt2HiNat n * d)
        = (sqrt2HiNat n * sqrt2HiNat n) * (d * d) :=
          nat_square_mul_square (sqrt2HiNat n) d
    _ < (p * p) * (powTwoNat n * powTwoNat n) := hcross
    _ = (p * powTwoNat n) * (p * powTwoNat n) :=
          (nat_square_mul_square p (powTwoNat n)).symm

private theorem int_neg_mul_one_lt_one_mul_nat (p d : Nat) :
    Int.negSucc p * 1 < 1 * Int.ofNat d := by
  change Int.mul (Int.negSucc p) (Int.ofNat 1) <
    Int.mul (Int.ofNat 1) (Int.ofNat d)
  change Int.negOfNat (Nat.succ p * 1) < Int.ofNat (1 * d)
  rw [nat_mul_one_local (Nat.succ p)]
  rw [Nat.one_mul]
  change Int.negSucc p < Int.ofNat d
  change Int.negSucc p + 1 <= Int.ofNat d
  apply (Int.le_def (a := Int.negSucc p + 1) (b := Int.ofNat d)).mpr
  change (Int.ofNat d - (Int.negSucc p + 1)).NonNeg
  cases p with
  | zero =>
      change (Int.ofNat d - Int.ofNat 0).NonNeg
      change (Int.ofNat d).NonNeg
      exact Int.NonNeg.mk d
  | succ p =>
      change (Int.ofNat d - Int.negSucc p).NonNeg
      unfold HSub.hSub Int.instSub Int.sub
      change (Int.ofNat d + -Int.negSucc p).NonNeg
      change (Int.ofNat d + Int.ofNat (p + 1)).NonNeg
      change (Int.ofNat (d + (p + 1))).NonNeg
      exact Int.NonNeg.mk (d + (p + 1))

private theorem apart_negative_nat (p d : Nat) (hd : 0 < d) :
    DReal.ApartRat sqrt2D { num := Int.negSucc p, den := d, den_pos := hd } := by
  refine ⟨0, Or.inl ?_⟩
  change Rat.lt { num := Int.negSucc p, den := d, den_pos := hd } (DReal.loQ sqrt2D 0)
  unfold DReal.loQ Rat.ofIntOverPowTwo sqrt2D sqrt2LoInt sqrt2LoNat
  unfold Rat.lt
  change Int.negSucc p * Int.ofNat 1 < Int.ofNat 1 * Int.ofNat d
  change Int.negSucc p * 1 < 1 * Int.ofNat d
  exact int_neg_mul_one_lt_one_mul_nat p d

private theorem sqrt2_sq_sign_nat (p d : Nat) :
    0 < p ->
      p * p < 2 * (d * d) ∨ 2 * (d * d) < p * p := by
  intro hp
  cases Nat.lt_trichotomy (p * p) (2 * (d * d)) with
  | inl below =>
      exact Or.inl below
  | inr rest =>
      cases rest with
      | inl same =>
          exact False.elim (nat_not_square_eq_two_square_pos p d hp same)
      | inr above =>
          exact Or.inr above

private theorem apart_positive_nat (p d : Nat) (hd : 0 < d) (hp : 0 < p) :
    DReal.ApartRat sqrt2D { num := Int.ofNat p, den := d, den_pos := hd } := by
  cases Nat.lt_or_ge p (Nat.succ d) with
  | inr pLarge =>
      have oneLeP : d + 1 <= p := pLarge
      have twoDLeTwoP : 2 * d <= 2 * p := Nat.mul_le_mul_left 2 (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self d) oneLeP))
      have twoDLeP_or_mid : 2 * d <= p ∨ p < 2 * d := by
        cases Nat.lt_or_ge p (2 * d) with
        | inl hlt => exact Or.inr hlt
        | inr hge => exact Or.inl hge
      cases twoDLeP_or_mid with
      | inl htwo =>
          exact apart_large_nat hd htwo
      | inr hmid =>
          cases sqrt2_sq_sign_nat p d hp with
          | inl below =>
              let n := 4 * (d * d) + 1
              have hgap : 4 * (d * d) < powTwoNat n := by
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (4 * (d * d)))
                  (powTwoNat_self_covers n)
              exact ⟨n, Or.inl (lower_rat_cross_of_gap hd hgap below)⟩
          | inr above =>
              let n := 4 * (d * d) + 1
              have hgap : 4 * (d * d) < powTwoNat n := by
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (4 * (d * d)))
                  (powTwoNat_self_covers n)
              exact ⟨n, Or.inr (upper_rat_cross_of_gap hd hgap above)⟩
  | inl pSmall =>
      have pLeD : p <= d := Nat.le_of_lt_succ pSmall
      exact apart_small_nat hd pLeD

theorem sqrt2_rat_apart :
    ∀ q : Rat, DReal.ApartRat sqrt2D q := by
  intro q
  cases q with
  | mk num den den_pos =>
      cases num with
      | ofNat p =>
          cases p with
          | zero =>
              exact apart_small_nat den_pos (Nat.zero_le den)
          | succ p =>
              exact apart_positive_nat (Nat.succ p) den den_pos (Nat.succ_pos p)
      | negSucc p =>
          exact apart_negative_nat p den den_pos

end BEDC.Real.DyadicIntervalStream
