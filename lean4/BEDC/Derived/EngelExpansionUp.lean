import BEDC.Derived.RationalUp

namespace BEDC.Derived.EngelExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.RationalUp

structure EngelRat where
  num : Nat
  den : Nat
  den_pos : 0 < den

structure EngelPositiveRat where
  num : Nat
  den : Nat
  num_pos : 0 < num
  den_pos : 0 < den

structure EngelTerm where
  val : Nat
  pos : 0 < val

def EngelPositiveRat.toRat (x : EngelPositiveRat) : EngelRat :=
  { num := x.num
    den := x.den
    den_pos := x.den_pos }

def EngelRatEq (x y : EngelRat) : Prop :=
  x.num * y.den = y.num * x.den

def engelZero : EngelRat :=
  { num := 0, den := 1, den_pos := Nat.succ_pos 0 }

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [Nat.left_distrib]
      rw [ih]

private theorem nat_add_shuffle_pure (x y a b : Nat) :
    (x + y) + (a + b) = (x + a) + (y + b) := by
  calc
    (x + y) + (a + b) = x + (y + (a + b)) := by
      rw [Nat.add_assoc]
    _ = x + ((y + a) + b) := by
      rw [← Nat.add_assoc y a b]
    _ = x + ((a + y) + b) := by
      rw [Nat.add_comm y a]
    _ = x + (a + (y + b)) := by
      rw [Nat.add_assoc a y b]
    _ = (x + a) + (y + b) := by
      rw [← Nat.add_assoc x a (y + b)]

private theorem nat_right_distrib_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [ih]
      exact nat_add_shuffle_pure (a * c) (b * c) a b

private theorem nat_mul_rotate_pure (a b c : Nat) :
    (a * b) * c = b * (a * c) := by
  calc
    (a * b) * c = a * (b * c) := nat_mul_assoc_pure a b c
    _ = (b * c) * a := Nat.mul_comm a (b * c)
    _ = b * (c * a) := nat_mul_assoc_pure b c a
    _ = b * (a * c) := by
      rw [Nat.mul_comm c a]

private theorem right_lt_succ_add_left (a b : Nat) :
    b < Nat.succ (a + b) := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.lt_succ_self b
  | succ a ih =>
      rw [Nat.succ_add]
      exact Nat.lt_trans ih (Nat.lt_succ_self _)

private theorem gap_lt_of_pos_left_add_eq {a gap n : Nat}
    (ha : 0 < a) (h : a + gap = n) :
    gap < n := by
  cases a with
  | zero =>
      cases ha
  | succ a =>
      rw [← h]
      rw [Nat.succ_add]
      exact right_lt_succ_add_left a gap

private theorem le_add_left_pure (a b : Nat) :
    b ≤ a + b := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.le_refl b
  | succ a ih =>
      rw [Nat.succ_add]
      exact Nat.le_trans ih (Nat.le_of_lt (Nat.lt_succ_self _))

private theorem le_add_right_pure (a b : Nat) :
    a ≤ a + b := by
  induction b with
  | zero =>
      rw [Nat.add_zero]
      exact Nat.le_refl a
  | succ b ih =>
      rw [Nat.add_succ]
      exact Nat.le_trans ih (Nat.le_of_lt (Nat.lt_succ_self _))

inductive NatCompareGap (a b : Nat) : Type where
  | le_gap (gap : Nat) (eqn : a + gap = b) : NatCompareGap a b
  | gt_gap (gap : Nat) (eqn : b + Nat.succ gap = a) : NatCompareGap a b

def natCompareGap : (a b : Nat) -> NatCompareGap a b
  | 0, b =>
      NatCompareGap.le_gap b
        (by
          rw [Nat.zero_add])
  | Nat.succ a, 0 =>
      NatCompareGap.gt_gap a
        (by
          rw [Nat.zero_add])
  | Nat.succ a, Nat.succ b =>
      match natCompareGap a b with
      | NatCompareGap.le_gap gap eqn =>
          NatCompareGap.le_gap gap
            (by
              rw [Nat.succ_add, eqn])
      | NatCompareGap.gt_gap gap eqn =>
          NatCompareGap.gt_gap gap
            (by
              rw [Nat.succ_add, eqn])

structure CeilData where
  q : Nat
  r : Nat

def ceilSegmentFuel : Nat -> Nat -> Nat -> CeilData
  | 0, _rem, _n => { q := 1, r := 0 }
  | fuel + 1, rem, n =>
      match natCompareGap rem n with
      | NatCompareGap.le_gap gap _ =>
          { q := 1, r := gap }
      | NatCompareGap.gt_gap rest _ =>
          let step := ceilSegmentFuel fuel (Nat.succ rest) n
          { q := Nat.succ step.q, r := step.r }

def ceilData (d n : Nat) : CeilData :=
  ceilSegmentFuel d d n

def ceilDiv (d n : Nat) : Nat :=
  (ceilData d n).q

theorem ceilSegmentFuel_sound (fuel rem n : Nat) :
    rem ≤ fuel -> 0 < rem -> 0 < n ->
      let step := ceilSegmentFuel fuel rem n
      0 < step.q ∧ step.r < n ∧ rem + step.r = step.q * n := by
  induction fuel generalizing rem with
  | zero =>
      intro hle hrem _hn
      cases rem with
      | zero =>
          cases hrem
      | succ rem =>
          exact False.elim (Nat.not_succ_le_zero rem hle)
  | succ fuel ih =>
      intro hle hrem hn
      unfold ceilSegmentFuel
      cases natCompareGap rem n with
      | le_gap gap hgap =>
          change 0 < 1 ∧ gap < n ∧ rem + gap = 1 * n
          constructor
          · exact Nat.succ_pos 0
          constructor
          · exact gap_lt_of_pos_left_add_eq hrem hgap
          · rw [Nat.one_mul]
            exact hgap
      | gt_gap rest hrest =>
          change
            0 < Nat.succ (ceilSegmentFuel fuel (Nat.succ rest) n).q ∧
              (ceilSegmentFuel fuel (Nat.succ rest) n).r < n ∧
                rem + (ceilSegmentFuel fuel (Nat.succ rest) n).r =
                  Nat.succ (ceilSegmentFuel fuel (Nat.succ rest) n).q * n
          have hrestFuel : Nat.succ rest ≤ fuel := by
            have hle' : n + Nat.succ rest ≤ Nat.succ fuel := by
              rw [hrest]
              exact hle
            cases n with
            | zero =>
                cases hn
            | succ n =>
                rw [Nat.succ_add] at hle'
                have lower : n + Nat.succ rest ≤ fuel :=
                  Nat.le_of_succ_le_succ hle'
                exact Nat.le_trans (le_add_left_pure n (Nat.succ rest)) lower
          have recData :=
            ih (Nat.succ rest) hrestFuel (Nat.succ_pos rest) hn
          change
            0 < (ceilSegmentFuel fuel (Nat.succ rest) n).q ∧
              (ceilSegmentFuel fuel (Nat.succ rest) n).r < n ∧
                Nat.succ rest + (ceilSegmentFuel fuel (Nat.succ rest) n).r =
                  (ceilSegmentFuel fuel (Nat.succ rest) n).q * n at recData
          constructor
          · exact Nat.succ_pos _
          constructor
          · exact recData.right.left
          · calc
              rem + (ceilSegmentFuel fuel (Nat.succ rest) n).r
                  = (n + Nat.succ rest) +
                      (ceilSegmentFuel fuel (Nat.succ rest) n).r := by
                      rw [hrest]
              _ = n +
                    (Nat.succ rest +
                      (ceilSegmentFuel fuel (Nat.succ rest) n).r) := by
                      rw [Nat.add_assoc]
              _ = n + (ceilSegmentFuel fuel (Nat.succ rest) n).q * n := by
                      rw [recData.right.right]
              _ = (ceilSegmentFuel fuel (Nat.succ rest) n).q * n + n := by
                      rw [Nat.add_comm]
              _ = Nat.succ (ceilSegmentFuel fuel (Nat.succ rest) n).q * n := by
                      rw [Nat.succ_mul]

theorem ceilData_sound {d n : Nat} (hd : 0 < d) (hn : 0 < n) :
    let step := ceilData d n
    0 < step.q ∧ step.r < n ∧ d + step.r = step.q * n := by
  unfold ceilData
  exact ceilSegmentFuel_sound d d n (Nat.le_refl d) hd hn

theorem ceilDiv_pos {d n : Nat} (hn : 0 < n) (hle : n ≤ d) :
    0 < ceilDiv d n := by
  unfold ceilDiv
  have sound := ceilData_sound (Nat.lt_of_lt_of_le hn hle) hn
  change 0 < (ceilData d n).q
  exact sound.left

theorem ceilDiv_pos_of_den {d n : Nat} (hn : 0 < n) (hd : 0 < d) :
    0 < ceilDiv d n := by
  unfold ceilDiv
  have sound := ceilData_sound hd hn
  change 0 < (ceilData d n).q
  exact sound.left

theorem ceilDiv_mul_ge {d n : Nat} (hn : 0 < n) :
    d ≤ ceilDiv d n * n := by
  cases d with
  | zero =>
      exact Nat.zero_le (ceilDiv 0 n * n)
  | succ d =>
      unfold ceilDiv
      have sound := ceilData_sound (Nat.succ_pos d) hn
      change Nat.succ d ≤ (ceilData (Nat.succ d) n).q * n
      have leftLe : Nat.succ d ≤ Nat.succ d + (ceilData (Nat.succ d) n).r :=
        le_add_right_pure (Nat.succ d) (ceilData (Nat.succ d) n).r
      rw [sound.right.right] at leftLe
      exact leftLe

def engelRemainder (x : EngelPositiveRat) : Nat :=
  (ceilData x.den x.num).r

theorem engelRemainder_lt_num (x : EngelPositiveRat) :
    engelRemainder x < x.num := by
  unfold engelRemainder
  exact (ceilData_sound x.den_pos x.num_pos).right.left

theorem engelRemainder_add_den (x : EngelPositiveRat) :
    x.den + engelRemainder x = ceilDiv x.den x.num * x.num := by
  unfold engelRemainder
  unfold ceilDiv
  exact (ceilData_sound x.den_pos x.num_pos).right.right

def engelHead (x : EngelPositiveRat) : EngelTerm :=
  { val := ceilDiv x.den x.num
    pos := ceilDiv_pos_of_den x.num_pos x.den_pos }

def engelFuel : Nat -> EngelPositiveRat -> List EngelTerm
  | 0, _x => []
  | fuel + 1, x =>
      let r := engelRemainder x
      if hr : r = 0 then
        [engelHead x]
      else
        engelHead x ::
          engelFuel fuel
            { num := r
              den := x.den
              num_pos := Nat.pos_of_ne_zero hr
              den_pos := x.den_pos }

def engel (x : EngelPositiveRat) : List EngelTerm :=
  engelFuel x.num x

def engelValue : List EngelTerm -> EngelRat
  | [] => engelZero
  | a :: tail =>
      let v := engelValue tail
      { num := v.den + v.num
        den := a.val * v.den
        den_pos := Nat.mul_pos a.pos v.den_pos }

theorem engelFuel_length_le (fuel : Nat) (x : EngelPositiveRat) :
    (engelFuel fuel x).length ≤ fuel := by
  induction fuel generalizing x with
  | zero =>
      exact Nat.le_refl 0
  | succ fuel ih =>
      unfold engelFuel
      by_cases hr : engelRemainder x = 0
      · rw [dif_pos hr]
        exact Nat.succ_le_succ (Nat.zero_le fuel)
      · rw [dif_neg hr]
        exact Nat.succ_le_succ (ih _)

theorem engel_finite_termination (x : EngelPositiveRat) :
    (engel x).length ≤ x.num := by
  unfold engel
  exact engelFuel_length_le x.num x

private theorem engelValue_cons_eq
    (a : EngelTerm) (tail : List EngelTerm) :
    engelValue (a :: tail) =
      { num := (engelValue tail).den + (engelValue tail).num
        den := a.val * (engelValue tail).den
        den_pos := Nat.mul_pos a.pos (engelValue tail).den_pos } := by
  rfl

private theorem engel_one_step_value (x : EngelPositiveRat)
    (hzero : engelRemainder x = 0) :
    EngelRatEq (engelValue [engelHead x]) x.toRat := by
  unfold EngelRatEq EngelPositiveRat.toRat engelHead
  change (1 + 0) * x.den = x.num * (ceilDiv x.den x.num * 1)
  unfold engelRemainder at hzero
  have productEq : ceilDiv x.den x.num * x.num = x.den := by
    have addEq := engelRemainder_add_den x
    unfold engelRemainder at addEq
    rw [hzero, Nat.add_zero] at addEq
    exact addEq.symm
  calc
    (1 + 0) * x.den = x.den := by rw [Nat.add_zero, Nat.one_mul]
    _ = x.num * (ceilDiv x.den x.num * 1) := by
        rw [Nat.mul_one]
        rw [Nat.mul_comm]
        exact productEq.symm

private theorem engel_cons_reconstruct
    (x : EngelPositiveRat) (tail : List EngelTerm)
    (tailEq : EngelRatEq (engelValue tail)
      { num := engelRemainder x, den := x.den, den_pos := x.toRat.den_pos }) :
    EngelRatEq (engelValue (engelHead x :: tail)) x.toRat := by
  unfold EngelRatEq at tailEq ⊢
  unfold EngelPositiveRat.toRat engelValue engelHead
  change
    ((engelValue tail).den + (engelValue tail).num) * x.den =
      x.num * (ceilDiv x.den x.num * (engelValue tail).den)
  have denRem : x.den + engelRemainder x = ceilDiv x.den x.num * x.num :=
    engelRemainder_add_den x
  have tailEq' :
      (engelValue tail).num * x.den =
        engelRemainder x * (engelValue tail).den := tailEq
  calc
    ((engelValue tail).den + (engelValue tail).num) * x.den
        = (engelValue tail).den * x.den +
            (engelValue tail).num * x.den := by
              exact
                nat_right_distrib_pure
                  (engelValue tail).den (engelValue tail).num x.den
    _ = (engelValue tail).den * x.den +
          engelRemainder x * (engelValue tail).den := by
              rw [tailEq']
    _ = x.den * (engelValue tail).den +
          engelRemainder x * (engelValue tail).den := by
              rw [Nat.mul_comm (engelValue tail).den x.den]
    _ = (x.den + engelRemainder x) * (engelValue tail).den := by
              exact
                (nat_right_distrib_pure
                    x.den (engelRemainder x) (engelValue tail).den).symm
    _ = (ceilDiv x.den x.num * x.num) * (engelValue tail).den := by
              rw [denRem]
    _ = x.num * (ceilDiv x.den x.num * (engelValue tail).den) := by
              exact
                nat_mul_rotate_pure
                  (ceilDiv x.den x.num) x.num (engelValue tail).den

theorem engelFuel_reconstruct
    (fuel : Nat) (x : EngelPositiveRat) :
    x.num ≤ fuel ->
      EngelRatEq (engelValue (engelFuel fuel x)) x.toRat := by
  induction fuel generalizing x with
  | zero =>
      intro hle
      exact False.elim (Nat.not_succ_le_zero (x.num - 1)
        (by
          have xpos : x.num = Nat.succ (x.num - 1) := by
            exact (Nat.sub_one_add_one (Nat.ne_of_gt x.num_pos)).symm
          rw [← xpos]
          exact hle))
  | succ fuel ih =>
      intro hle
      unfold engelFuel
      by_cases hr : engelRemainder x = 0
      · rw [dif_pos hr]
        exact engel_one_step_value x hr
      · rw [dif_neg hr]
        apply engel_cons_reconstruct
        apply ih
        exact Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le (engelRemainder_lt_num x) hle)

theorem engel_reconstruct (x : EngelPositiveRat) :
    EngelRatEq (engelValue (engel x)) x.toRat := by
  unfold engel
  exact engelFuel_reconstruct x.num x (Nat.le_refl x.num)

private abbrev unaryOne : BHist :=
  BHist.e1 BHist.Empty

private theorem natToUnary_one_left_cont (n : Nat) :
    BEDC.FKernel.Cont.Cont unaryOne (natToUnary n)
      (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1 (BEDC.FKernel.Cont.append unaryOne _)
      exact congrArg BHist.e1 ih

private theorem natToUnary_den_pos {n : Nat} (hn : 0 < n) :
    NatUnaryStrictPrefix unaryOne (natToUnary n) ∨
      hsame (natToUnary n) unaryOne := by
  cases n with
  | zero =>
      cases hn
  | succ n =>
      cases n with
      | zero =>
          exact Or.inr rfl
      | succ n =>
          exact Or.inl
            ⟨natToUnary (Nat.succ n), natToUnary_unary (Nat.succ n),
              (fun empty => by cases empty),
              natToUnary_one_left_cont (Nat.succ n)⟩

def EngelRat.toRatNum (x : EngelRat) : RatNum :=
  { num := intOfNat (natToUnary x.num) (natToUnary_unary x.num)
    den := natToUnary x.den
    den_pos := natToUnary_den_pos x.den_pos }

def EngelPositiveRat.toRatNum (x : EngelPositiveRat) : RatNum :=
  x.toRat.toRatNum

def engelValueRatNum (terms : List EngelTerm) : RatNum :=
  (engelValue terms).toRatNum

def engelInputRatNum (x : EngelPositiveRat) : RatNum :=
  x.toRatNum

end BEDC.Derived.EngelExpansionUp
