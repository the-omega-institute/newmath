import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.PrimeUp.ResultBoundary
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.RationalUp.FieldLaws

namespace BEDC.Derived.GcdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp

def NatGcd (a b g : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory g ∧
    NatDivides g a ∧ NatDivides g b ∧
      ∀ d : BHist, NatDivides d a -> NatDivides d b -> NatDivides d g

theorem NatGcd_left_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory a := by
  intro gcd
  exact gcd.left

theorem NatGcd_right_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory b := by
  intro gcd
  exact gcd.right.left

theorem NatGcd_result_unary {a b g : BHist} :
    NatGcd a b g -> UnaryHistory g := by
  intro gcd
  exact gcd.right.right.left

theorem NatGcd_dvd_left {a b g : BHist} :
    NatGcd a b g -> NatDivides g a := by
  intro gcd
  exact gcd.right.right.right.left

theorem NatGcd_dvd_right {a b g : BHist} :
    NatGcd a b g -> NatDivides g b := by
  intro gcd
  exact gcd.right.right.right.right.left

theorem NatGcd_greatest {a b g d : BHist} :
    NatGcd a b g -> NatDivides d a -> NatDivides d b -> NatDivides d g := by
  intro gcd
  exact gcd.right.right.right.right.right d

private theorem NatDivides_empty_divisor_succ_absurd {d b : BHist} :
    hsame d BHist.Empty -> NatDivides d b -> UnaryHistory b ->
      (hsame b BHist.Empty -> False) -> False := by
  intro dEmpty divides bUnary bNonempty
  cases dEmpty
  exact bNonempty (NatDivides_empty_left_result_empty divides)

theorem NatGcd_unique_hsame {a b g h : BHist} :
    NatGcd a b g -> NatGcd a b h -> hsame g h := by
  intro left right
  have gDividesH : NatDivides g h :=
    NatGcd_greatest right (NatGcd_dvd_left left) (NatGcd_dvd_right left)
  have hDividesG : NatDivides h g :=
    NatGcd_greatest left (NatGcd_dvd_left right) (NatGcd_dvd_right right)
  exact NatDivides_antisymmetry_hsame
    (NatGcd_result_unary left) (NatGcd_result_unary right) gDividesH hDividesG

theorem NatGcd_zero_right {a : BHist} :
    UnaryHistory a -> NatGcd a BHist.Empty a := by
  intro aUnary
  constructor
  · exact aUnary
  · constructor
    · exact unary_empty
    · constructor
      · exact aUnary
      · constructor
        · exact (NatDivides_reflexive_pair aUnary).right
        · constructor
          · exact NatDivides_empty_right_iff.mpr aUnary
          · intro d dividesA _dividesZero
            exact dividesA

private theorem NatDivRem_divisor_nonempty {b a q r : BHist} :
    NatDivRem b a q r -> hsame b BHist.Empty -> False := by
  intro divrem bEmpty
  cases divrem with
  | intro _mq data =>
      cases bEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd data.right.right

private theorem NatDivRem_common_divisor_remainder {a b q r d : BHist} :
    NatDivRem b a q r -> NatDivides d a -> NatDivides d b -> NatDivides d r := by
  intro divrem dividesA dividesB
  cases divrem with
  | intro bq data =>
      have dUnary : UnaryHistory d := NatDivides_divisor_unary dividesA
      have bNonempty : hsame b BHist.Empty -> False := by
        intro bEmpty
        cases bEmpty
        exact NatUnaryStrictPrefix_empty_right_absurd data.right.right
      have dNonempty : hsame d BHist.Empty -> False := by
        intro dEmpty
        exact NatDivides_empty_divisor_succ_absurd dEmpty dividesB
          (NatMul_left_unary data.left) bNonempty
      have bDividesProduct : NatDivides b bq :=
        ⟨q, NatMul_right_unary data.left, data.left⟩
      have dDividesProduct : NatDivides d bq :=
        NatDivides_transitive dividesB bDividesProduct
      exact dvd_tail_of_dvd_sum dUnary dNonempty data.right.left dDividesProduct dividesA

private theorem NatDivRem_common_divisor_dividend {a b q r d : BHist} :
    NatDivRem b a q r -> NatDivides d b -> NatDivides d r -> NatDivides d a := by
  intro divrem dividesB dividesR
  cases divrem with
  | intro bq data =>
      have bDividesProduct : NatDivides b bq :=
        ⟨q, NatMul_right_unary data.left, data.left⟩
      have dDividesProduct : NatDivides d bq :=
        NatDivides_transitive dividesB bDividesProduct
      exact NatDivides_cont_closed dDividesProduct dividesR data.right.left.right.right

theorem NatGcd_of_divrem {a b q r g : BHist} :
    NatDivRem b a q r -> NatGcd b r g -> NatGcd a b g := by
  intro divrem tailGcd
  constructor
  · exact NatDivRem_dividend_unary divrem
  · constructor
    · exact NatDivRem_divisor_unary divrem
    · constructor
      · exact NatGcd_result_unary tailGcd
      · constructor
        · exact NatDivRem_common_divisor_dividend divrem
            (NatGcd_dvd_left tailGcd) (NatGcd_dvd_right tailGcd)
        · constructor
          · exact NatGcd_dvd_left tailGcd
          · intro d dividesA dividesB
            have dividesR : NatDivides d r :=
              NatDivRem_common_divisor_remainder divrem dividesA dividesB
            exact NatGcd_greatest tailGcd dividesB dividesR

def natGcdFuel : Nat -> BHist -> BHist -> BHist
  | 0, a, _b => a
  | _fuel + 1, a, BHist.Empty => a
  | _fuel + 1, a, BHist.e0 _tail => a
  | fuel + 1, a, BHist.e1 tail =>
      natGcdFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)

def natGcdFn (a b : BHist) : BHist :=
  natGcdFuel (BEDC.FKernel.ExternalBinary.bwordLength b + 1) a b

theorem natGcdFuel_spec {fuel : Nat} {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      BEDC.FKernel.ExternalBinary.bwordLength b < fuel ->
        NatGcd a b (natGcdFuel fuel a b) := by
  intro aUnary bUnary fuelEnough
  induction fuel generalizing a b with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ fuelEnough)
  | succ fuel ih =>
      cases b with
      | Empty =>
          exact NatGcd_zero_right aUnary
      | e0 tail =>
          cases bUnary
      | e1 tail =>
          have bNonempty : hsame (BHist.e1 tail) BHist.Empty -> False := by
            intro empty
            exact not_hsame_e1_empty empty
          have remUnary : UnaryHistory (natModFn (BHist.e1 tail) a) :=
            natModFn_unary (unary_e1_closed bUnary) aUnary bNonempty
          have remStrict :
              NatUnaryStrictPrefix (natModFn (BHist.e1 tail) a) (BHist.e1 tail) :=
            natModFn_lt (unary_e1_closed bUnary) aUnary bNonempty
          have remLengthLtB :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) <
                BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) :=
            NatUnaryStrictPrefix_length_lt remUnary remStrict
          have bLengthLeFuel :
              BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) ≤ fuel :=
            Nat.lt_succ_iff.mp fuelEnough
          have remFuelEnough :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) < fuel :=
            Nat.lt_of_lt_of_le remLengthLtB bLengthLeFuel
          have tailGcd :
              NatGcd (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
                (natGcdFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)) :=
            ih (unary_e1_closed bUnary) remUnary remFuelEnough
          have divrem :
              NatDivRem (BHist.e1 tail) a
                (natQuotFn (BHist.e1 tail) a) (natModFn (BHist.e1 tail) a) :=
            natModFn_spec (unary_e1_closed bUnary) aUnary bNonempty
          exact NatGcd_of_divrem divrem tailGcd

theorem natGcdFn_spec {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> NatGcd a b (natGcdFn a b) := by
  intro aUnary bUnary
  unfold natGcdFn
  exact natGcdFuel_spec aUnary bUnary (Nat.lt_succ_self _)

def NatBezoutEquation (a b g : BHist) (x y : BHist × BHist) : Prop :=
  IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 ∧
    IntPairClassifier
      (pairAdd (pairMul x (a, BHist.Empty)) (pairMul y (b, BHist.Empty)))
      (g, BHist.Empty)

theorem NatBezoutEquation_carriers {a b g : BHist} {x y : BHist × BHist} :
    NatBezoutEquation a b g x y ->
      IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 := by
  intro bezout
  exact ⟨bezout.left, bezout.right.left⟩

private theorem IntPairClassifier_trans_pair {x y z : BHist × BHist} :
    IntPairClassifier x y -> IntPairClassifier y z -> IntPairClassifier x z := by
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left

theorem NatBezout_zero_right {a : BHist} :
    UnaryHistory a ->
      NatBezoutEquation a BHist.Empty a
        (NatOne, BHist.Empty) (BHist.Empty, BHist.Empty) := by
  intro aUnary
  have xCarrier : IntPairCarrier NatOne BHist.Empty :=
    ⟨unary_e1_closed unary_empty, unary_empty⟩
  have yCarrier : IntPairCarrier BHist.Empty BHist.Empty :=
    ⟨unary_empty, unary_empty⟩
  constructor
  · exact xCarrier
  · constructor
    · exact yCarrier
    · have leftUnit :
          IntPairClassifier (pairMul (NatOne, BHist.Empty) (a, BHist.Empty))
            (a, BHist.Empty) :=
        pairMul_unit_left (a, BHist.Empty) ⟨aUnary, unary_empty⟩
      have rightZero :
          IntPairClassifier (pairMul (BHist.Empty, BHist.Empty) (BHist.Empty, BHist.Empty))
            (BHist.Empty, BHist.Empty) :=
        pairMul_zero_right (BHist.Empty, BHist.Empty) yCarrier
      have addTransport :
          IntPairClassifier
            (pairAdd (pairMul (NatOne, BHist.Empty) (a, BHist.Empty))
              (pairMul (BHist.Empty, BHist.Empty) (BHist.Empty, BHist.Empty)))
            (pairAdd (a, BHist.Empty) (BHist.Empty, BHist.Empty)) :=
        pairAdd_classifier_congr leftUnit rightZero
      exact IntPairClassifier_trans_pair addTransport
        (pairAdd_zero_right (a, BHist.Empty) ⟨aUnary, unary_empty⟩)

private theorem pairMul_nat_right_pos_length (x : BHist × BHist) (n : BHist)
    (hx : IntPairCarrier x.1 x.2) (hn : UnaryHistory n) :
    bwordLength (pairMul x (n, BHist.Empty)).1 =
      bwordLength x.1 * bwordLength n := by
  rw [pairMul_pos_length x (n, BHist.Empty) hx ⟨hn, unary_empty⟩]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.mul_zero, Nat.add_zero]

private theorem pairMul_nat_right_neg_length (x : BHist × BHist) (n : BHist)
    (hx : IntPairCarrier x.1 x.2) (hn : UnaryHistory n) :
    bwordLength (pairMul x (n, BHist.Empty)).2 =
      bwordLength x.2 * bwordLength n := by
  rw [pairMul_neg_length x (n, BHist.Empty) hx ⟨hn, unary_empty⟩]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.mul_zero, Nat.zero_add]

private theorem pairMul_nat_left_pos_length (n : BHist) (x : BHist × BHist)
    (hn : UnaryHistory n) (hx : IntPairCarrier x.1 x.2) :
    bwordLength (pairMul (n, BHist.Empty) x).1 =
      bwordLength n * bwordLength x.1 := by
  rw [pairMul_pos_length (n, BHist.Empty) x ⟨hn, unary_empty⟩ hx]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.zero_mul, Nat.add_zero]

private theorem pairMul_nat_left_neg_length (n : BHist) (x : BHist × BHist)
    (hn : UnaryHistory n) (hx : IntPairCarrier x.1 x.2) :
    bwordLength (pairMul (n, BHist.Empty) x).2 =
      bwordLength n * bwordLength x.2 := by
  rw [pairMul_neg_length (n, BHist.Empty) x ⟨hn, unary_empty⟩ hx]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.zero_mul, Nat.add_zero]

private theorem intSub_nat_mul_left_pos_length (x y : BHist × BHist) (q : BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2)
    (qUnary : UnaryHistory q) :
    bwordLength (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y)).1 =
      bwordLength x.1 + bwordLength q * bwordLength y.2 := by
  have qyCarrier : IntPairCarrier (pairMul (q, BHist.Empty) y).1
      (pairMul (q, BHist.Empty) y).2 :=
    pairMul_carrier ⟨qUnary, unary_empty⟩ hy
  unfold BEDC.Derived.IntUp.intSub
  rw [pairAdd_pos_length x (pairNeg (pairMul (q, BHist.Empty) y)) hx
    (pairNeg_carrier qyCarrier)]
  unfold pairNeg
  rw [pairMul_nat_left_neg_length q y qUnary hy]

private theorem intSub_nat_mul_left_neg_length (x y : BHist × BHist) (q : BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2)
    (qUnary : UnaryHistory q) :
    bwordLength (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y)).2 =
      bwordLength x.2 + bwordLength q * bwordLength y.1 := by
  have qyCarrier : IntPairCarrier (pairMul (q, BHist.Empty) y).1
      (pairMul (q, BHist.Empty) y).2 :=
    pairMul_carrier ⟨qUnary, unary_empty⟩ hy
  unfold BEDC.Derived.IntUp.intSub
  rw [pairAdd_neg_length x (pairNeg (pairMul (q, BHist.Empty) y)) hx
    (pairNeg_carrier qyCarrier)]
  unfold pairNeg
  rw [pairMul_nat_left_pos_length q y qUnary hy]

private theorem NatBezoutEquation_length_eq {a b g : BHist} {x y : BHist × BHist} :
    UnaryHistory a -> UnaryHistory b -> NatBezoutEquation a b g x y ->
      bwordLength x.1 * bwordLength a + bwordLength y.1 * bwordLength b =
        bwordLength g +
          (bwordLength x.2 * bwordLength a + bwordLength y.2 * bwordLength b) := by
  intro aUnary bUnary bezout
  have xCarrier : IntPairCarrier x.1 x.2 := bezout.left
  have yCarrier : IntPairCarrier y.1 y.2 := bezout.right.left
  have leftCarrier :
      IntPairCarrier
        (pairAdd (pairMul x (a, BHist.Empty)) (pairMul y (b, BHist.Empty))).1
        (pairAdd (pairMul x (a, BHist.Empty)) (pairMul y (b, BHist.Empty))).2 :=
    pairAdd_carrier
      (pairMul_carrier xCarrier ⟨aUnary, unary_empty⟩)
      (pairMul_carrier yCarrier ⟨bUnary, unary_empty⟩)
  have targetCarrier : IntPairCarrier g BHist.Empty := bezout.right.right.right.left
  have raw := IntPairClassifier_length_eq bezout.right.right
  rw [pairAdd_pos_length (pairMul x (a, BHist.Empty))
      (pairMul y (b, BHist.Empty))
      (pairMul_carrier xCarrier ⟨aUnary, unary_empty⟩)
      (pairMul_carrier yCarrier ⟨bUnary, unary_empty⟩)] at raw
  rw [pairAdd_neg_length (pairMul x (a, BHist.Empty))
      (pairMul y (b, BHist.Empty))
      (pairMul_carrier xCarrier ⟨aUnary, unary_empty⟩)
      (pairMul_carrier yCarrier ⟨bUnary, unary_empty⟩)] at raw
  rw [pairMul_nat_right_pos_length x a xCarrier aUnary] at raw
  rw [pairMul_nat_right_pos_length y b yCarrier bUnary] at raw
  rw [pairMul_nat_right_neg_length x a xCarrier aUnary] at raw
  rw [pairMul_nat_right_neg_length y b yCarrier bUnary] at raw
  rw [NatUp_unary_standard_bridge.left, Nat.add_zero] at raw
  exact raw

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_right_distrib_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun x => x + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun x => a * c + x) (Nat.mul_comm c b)

private theorem nat_mul_left_comm_clean (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (nat_mul_assoc_clean a b c).symm
    _ = (b * a) * c := congrArg (fun t => t * c) (Nat.mul_comm a b)
    _ = b * (a * c) := nat_mul_assoc_clean b a c

private theorem nat_mul_right_cycle_clean (a b c : Nat) :
    a * (b * c) = (c * a) * b := by
  calc
    a * (b * c) = b * (a * c) := nat_mul_left_comm_clean a b c
    _ = b * (c * a) := congrArg (fun t => b * t) (Nat.mul_comm a c)
    _ = (c * a) * b := Nat.mul_comm b (c * a)

private theorem nat_add_four_swap_clean (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_add_four_last_swap_clean (a b c d : Nat) :
    (a + b) + (c + d) = (a + d) + (c + b) := by
  calc
    (a + b) + (c + d) = (a + b) + (d + c) :=
      congrArg (fun t => (a + b) + t) (Nat.add_comm c d)
    _ = (a + d) + (b + c) := nat_add_four_swap_clean a b d c
    _ = (a + d) + (c + b) := congrArg (fun t => (a + d) + t) (Nat.add_comm b c)

private theorem nat_add_four_pair_rotate_clean (a b c d : Nat) :
    (a + b) + (c + d) = (c + b) + (a + d) := by
  calc
    (a + b) + (c + d) = (a + d) + (c + b) :=
      nat_add_four_last_swap_clean a b c d
    _ = (c + b) + (a + d) := Nat.add_comm (a + d) (c + b)

private theorem nat_add_four_tail_cycle_clean (a b c d : Nat) :
    (a + b) + (c + d) = (b + d) + (a + c) := by
  calc
    (a + b) + (c + d) = (a + c) + (b + d) :=
      nat_add_four_swap_clean a b c d
    _ = (b + d) + (a + c) := Nat.add_comm (a + c) (b + d)

private theorem nat_add_gcd_step_shuffle_clean (G a b c d : Nat) :
    (G + (a + b)) + (c + d) = G + ((b + d) + (a + c)) := by
  calc
    (G + (a + b)) + (c + d) = G + ((a + b) + (c + d)) :=
      Nat.add_assoc G (a + b) (c + d)
    _ = G + ((b + d) + (a + c)) :=
      congrArg (fun t => G + t) (nat_add_four_tail_cycle_clean a b c d)

private theorem nat_bezout_step_length_eq
    (A B Q R G xp xn yp yn : Nat)
    (div : A = B * Q + R)
    (tail : xp * B + yp * R = G + (xn * B + yn * R)) :
    yp * A + (xp + Q * yn) * B =
      G + (yn * A + (xn + Q * yp) * B) := by
  subst A
  have ypq : yp * (B * Q) = (Q * yp) * B := by
    exact nat_mul_right_cycle_clean yp B Q
  have ynq : yn * (B * Q) = (Q * yn) * B := by
    exact nat_mul_right_cycle_clean yn B Q
  have foldYn : yn * R + yn * (B * Q) = yn * (B * Q + R) := by
    calc
      yn * R + yn * (B * Q) = yn * (B * Q) + yn * R :=
        Nat.add_comm (yn * R) (yn * (B * Q))
      _ = yn * (B * Q + R) := (Nat.left_distrib yn (B * Q) R).symm
  calc
    yp * (B * Q + R) + (xp + Q * yn) * B
        = (yp * (B * Q) + yp * R) + (xp * B + (Q * yn) * B) := by
          rw [Nat.left_distrib, nat_right_distrib_clean]
    _ = ((Q * yp) * B + yp * R) + (xp * B + (Q * yn) * B) := by
          rw [ypq]
    _ = (xp * B + yp * R) + ((Q * yp) * B + (Q * yn) * B) := by
          exact nat_add_four_pair_rotate_clean ((Q * yp) * B) (yp * R)
            (xp * B) ((Q * yn) * B)
    _ = (G + (xn * B + yn * R)) + ((Q * yp) * B + (Q * yn) * B) := by
          rw [tail]
    _ = G + ((yn * R + (Q * yn) * B) + (xn * B + (Q * yp) * B)) := by
          exact nat_add_gcd_step_shuffle_clean G (xn * B) (yn * R)
            ((Q * yp) * B) ((Q * yn) * B)
    _ = G + ((yn * R + yn * (B * Q)) + (xn * B + (Q * yp) * B)) := by
          rw [ynq.symm]
    _ = G + (yn * (B * Q + R) + (xn + Q * yp) * B) := by
          rw [foldYn, (nat_right_distrib_clean xn (Q * yp) B).symm]

theorem NatBezout_of_divrem {a b q r g : BHist} {x y : BHist × BHist} :
    NatDivRem b a q r -> NatBezoutEquation b r g x y ->
      NatBezoutEquation a b g y
        (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y)) := by
  intro divrem tailBezout
  cases divrem with
  | intro bq data =>
      have bUnary : UnaryHistory b := NatMul_left_unary data.left
      have qUnary : UnaryHistory q := NatMul_right_unary data.left
      have bqUnary : UnaryHistory bq := NatMul_result_unary bUnary data.left
      have rUnary : UnaryHistory r := NatAdd_right_unary data.right.left
      have aUnary : UnaryHistory a := NatAdd_result_unary data.right.left
      have xCarrier : IntPairCarrier x.1 x.2 := tailBezout.left
      have yCarrier : IntPairCarrier y.1 y.2 := tailBezout.right.left
      have qyCarrier : IntPairCarrier (pairMul (q, BHist.Empty) y).1
          (pairMul (q, BHist.Empty) y).2 :=
        pairMul_carrier ⟨qUnary, unary_empty⟩ yCarrier
      have subCarrier : IntPairCarrier
          (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y)).1
          (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y)).2 :=
        intSub_carrier xCarrier qyCarrier
      have gCarrier : IntPairCarrier g BHist.Empty :=
        tailBezout.right.right.right.left
      constructor
      · exact yCarrier
      · constructor
        · exact subCarrier
        · apply IntPairClassifier_of_length_eq
            (pairAdd_carrier
              (pairMul_carrier yCarrier ⟨aUnary, unary_empty⟩)
              (pairMul_carrier subCarrier ⟨bUnary, unary_empty⟩))
            gCarrier
          have divLength :
              bwordLength a = bwordLength b * bwordLength q + bwordLength r := by
            calc
              bwordLength a = bwordLength bq + bwordLength r :=
                NatAdd_length data.right.left
              _ = bwordLength b * bwordLength q + bwordLength r := by
                rw [NatMul_bwordLength data.left]
          have tailLength :
              bwordLength x.1 * bwordLength b + bwordLength y.1 * bwordLength r =
                bwordLength g +
                  (bwordLength x.2 * bwordLength b + bwordLength y.2 * bwordLength r) :=
            NatBezoutEquation_length_eq bUnary rUnary tailBezout
          have numeric :=
            nat_bezout_step_length_eq
              (bwordLength a) (bwordLength b) (bwordLength q) (bwordLength r)
              (bwordLength g) (bwordLength x.1) (bwordLength x.2)
              (bwordLength y.1) (bwordLength y.2)
              divLength tailLength
          calc
            bwordLength
                (pairAdd (pairMul y (a, BHist.Empty))
                  (pairMul (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                    (b, BHist.Empty))).1 +
                bwordLength BHist.Empty
                = bwordLength y.1 * bwordLength a +
                    (bwordLength x.1 + bwordLength q * bwordLength y.2) *
                      bwordLength b := by
                  rw [pairAdd_pos_length (pairMul y (a, BHist.Empty))
                    (pairMul (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                      (b, BHist.Empty))
                    (pairMul_carrier yCarrier ⟨aUnary, unary_empty⟩)
                    (pairMul_carrier subCarrier ⟨bUnary, unary_empty⟩)]
                  rw [pairMul_nat_right_pos_length y a yCarrier aUnary]
                  rw [pairMul_nat_right_pos_length
                    (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                    b subCarrier bUnary]
                  rw [intSub_nat_mul_left_pos_length x y q xCarrier yCarrier qUnary]
                  rw [NatUp_unary_standard_bridge.left, Nat.add_zero]
            _ = bwordLength g +
                  (bwordLength y.2 * bwordLength a +
                    (bwordLength x.2 + bwordLength q * bwordLength y.1) *
                      bwordLength b) := numeric
            _ = bwordLength g +
                bwordLength
                  (pairAdd (pairMul y (a, BHist.Empty))
                    (pairMul (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                      (b, BHist.Empty))).2 := by
                  rw [pairAdd_neg_length (pairMul y (a, BHist.Empty))
                    (pairMul (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                      (b, BHist.Empty))
                    (pairMul_carrier yCarrier ⟨aUnary, unary_empty⟩)
                    (pairMul_carrier subCarrier ⟨bUnary, unary_empty⟩)]
                  rw [pairMul_nat_right_neg_length y a yCarrier aUnary]
                  rw [pairMul_nat_right_neg_length
                    (BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))
                    b subCarrier bUnary]
                  rw [intSub_nat_mul_left_neg_length x y q xCarrier yCarrier qUnary]

def NatBezoutCoefficients (a b g : BHist) : Prop :=
  ∃ x : BHist × BHist, ∃ y : BHist × BHist,
    NatBezoutEquation a b g x y

def natBezoutFuel : Nat -> BHist -> BHist -> (BHist × BHist) × (BHist × BHist)
  | 0, _a, _b => ((BHist.Empty, BHist.Empty), (BHist.Empty, BHist.Empty))
  | _fuel + 1, _a, BHist.Empty =>
      (((BEDC.Derived.PadicUp.NatOne), BHist.Empty), (BHist.Empty, BHist.Empty))
  | _fuel + 1, _a, BHist.e0 _tail =>
      ((BHist.Empty, BHist.Empty), (BHist.Empty, BHist.Empty))
  | fuel + 1, a, BHist.e1 tail =>
      let recCoeffs := natBezoutFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
      let x := recCoeffs.1
      let y := recCoeffs.2
      let q := natQuotFn (BHist.e1 tail) a
      (y, BEDC.Derived.IntUp.intSub x (pairMul (q, BHist.Empty) y))

def natBezoutFn (a b : BHist) : (BHist × BHist) × (BHist × BHist) :=
  natBezoutFuel (BEDC.FKernel.ExternalBinary.bwordLength b + 1) a b

private theorem nat_pair_sub_carrier {x y : BHist × BHist} :
    IntPairCarrier x.1 x.2 -> IntPairCarrier y.1 y.2 ->
      IntPairCarrier (BEDC.Derived.IntUp.intSub x y).1
        (BEDC.Derived.IntUp.intSub x y).2 := by
  intro hx hy
  exact intSub_carrier hx hy

theorem natBezoutFuel_carrier {fuel : Nat} {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      IntPairCarrier (natBezoutFuel fuel a b).1.1 (natBezoutFuel fuel a b).1.2 ∧
        IntPairCarrier (natBezoutFuel fuel a b).2.1 (natBezoutFuel fuel a b).2.2 := by
  intro aUnary bUnary
  induction fuel generalizing a b with
  | zero =>
      exact ⟨⟨unary_empty, unary_empty⟩, ⟨unary_empty, unary_empty⟩⟩
  | succ fuel ih =>
      cases b with
      | Empty =>
          exact
            ⟨⟨unary_e1_closed unary_empty, unary_empty⟩,
              ⟨unary_empty, unary_empty⟩⟩
      | e0 tail =>
          cases bUnary
      | e1 tail =>
          have bNonempty : hsame (BHist.e1 tail) BHist.Empty -> False := by
            intro empty
            exact not_hsame_e1_empty empty
          have remUnary : UnaryHistory (natModFn (BHist.e1 tail) a) :=
            natModFn_unary (unary_e1_closed bUnary) aUnary bNonempty
          let recCoeffs :=
            natBezoutFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
          let x := recCoeffs.1
          let y := recCoeffs.2
          have recCarrier :
              IntPairCarrier x.1 x.2 ∧ IntPairCarrier y.1 y.2 := by
            exact ih (unary_e1_closed bUnary) remUnary
          have qUnary : UnaryHistory (natQuotFn (BHist.e1 tail) a) :=
            NatDivRem_quotient_unary
              (natModFn_spec (unary_e1_closed bUnary) aUnary bNonempty)
          have qPairCarrier : IntPairCarrier (natQuotFn (BHist.e1 tail) a) BHist.Empty :=
            ⟨qUnary, unary_empty⟩
          change
            IntPairCarrier y.1 y.2 ∧
              IntPairCarrier
                (BEDC.Derived.IntUp.intSub x (pairMul (natQuotFn (BHist.e1 tail) a, BHist.Empty) y)).1
                (BEDC.Derived.IntUp.intSub x (pairMul (natQuotFn (BHist.e1 tail) a, BHist.Empty) y)).2
          exact
            ⟨recCarrier.right,
              nat_pair_sub_carrier recCarrier.left
                (pairMul_carrier qPairCarrier recCarrier.right)⟩

theorem natBezoutFn_carrier {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      IntPairCarrier (natBezoutFn a b).1.1 (natBezoutFn a b).1.2 ∧
        IntPairCarrier (natBezoutFn a b).2.1 (natBezoutFn a b).2.2 := by
  intro aUnary bUnary
  unfold natBezoutFn
  exact natBezoutFuel_carrier aUnary bUnary

theorem natBezoutFuel_spec {fuel : Nat} {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      BEDC.FKernel.ExternalBinary.bwordLength b < fuel ->
        NatBezoutEquation a b (natGcdFuel fuel a b)
          (natBezoutFuel fuel a b).1 (natBezoutFuel fuel a b).2 := by
  intro aUnary bUnary fuelEnough
  induction fuel generalizing a b with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ fuelEnough)
  | succ fuel ih =>
      cases b with
      | Empty =>
          exact NatBezout_zero_right aUnary
      | e0 tail =>
          cases bUnary
      | e1 tail =>
          have bNonempty : hsame (BHist.e1 tail) BHist.Empty -> False := by
            intro empty
            exact not_hsame_e1_empty empty
          have bUnary' : UnaryHistory (BHist.e1 tail) :=
            unary_e1_closed bUnary
          have remUnary : UnaryHistory (natModFn (BHist.e1 tail) a) :=
            natModFn_unary bUnary' aUnary bNonempty
          have remStrict :
              NatUnaryStrictPrefix (natModFn (BHist.e1 tail) a) (BHist.e1 tail) :=
            natModFn_lt bUnary' aUnary bNonempty
          have remLengthLtB :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) <
                BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) :=
            NatUnaryStrictPrefix_length_lt remUnary remStrict
          have bLengthLeFuel :
              BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 tail) ≤ fuel :=
            Nat.lt_succ_iff.mp fuelEnough
          have remFuelEnough :
              BEDC.FKernel.ExternalBinary.bwordLength (natModFn (BHist.e1 tail) a) < fuel :=
            Nat.lt_of_lt_of_le remLengthLtB bLengthLeFuel
          have tailBezout :
              NatBezoutEquation (BHist.e1 tail) (natModFn (BHist.e1 tail) a)
                (natGcdFuel fuel (BHist.e1 tail) (natModFn (BHist.e1 tail) a))
                (natBezoutFuel fuel (BHist.e1 tail)
                  (natModFn (BHist.e1 tail) a)).1
                (natBezoutFuel fuel (BHist.e1 tail)
                  (natModFn (BHist.e1 tail) a)).2 :=
            ih bUnary' remUnary remFuelEnough
          have divrem :
              NatDivRem (BHist.e1 tail) a
                (natQuotFn (BHist.e1 tail) a) (natModFn (BHist.e1 tail) a) :=
            natModFn_spec bUnary' aUnary bNonempty
          exact NatBezout_of_divrem divrem tailBezout

theorem natBezoutFn_spec {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      NatBezoutEquation a b (natGcdFn a b)
        (natBezoutFn a b).1 (natBezoutFn a b).2 := by
  intro aUnary bUnary
  unfold natBezoutFn natGcdFn
  exact natBezoutFuel_spec aUnary bUnary (Nat.lt_succ_self _)

theorem NatBezoutCoefficients_natGcdFn {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      NatBezoutCoefficients a b (natGcdFn a b) := by
  intro aUnary bUnary
  exact ⟨(natBezoutFn a b).1, (natBezoutFn a b).2,
    natBezoutFn_spec aUnary bUnary⟩

def natBezoutIntegerX (a b : BHist) : IntegerUp :=
  pairToInt (natBezoutFn a b).1

def natBezoutIntegerY (a b : BHist) : IntegerUp :=
  pairToInt (natBezoutFn a b).2

def NatBezoutIntegerEquation
    (a b g : BHist) (aUnary : UnaryHistory a) (bUnary : UnaryHistory b)
    (gUnary : UnaryHistory g) (x y : IntegerUp) : Prop :=
  IntEq
    (IntAdd
      (IntMul x (intOfNat a aUnary))
      (IntMul y (intOfNat b bUnary)))
    (intOfNat g gUnary)

theorem NatBezoutIntegerEquation_of_pair
    {a b g : BHist} {aUnary : UnaryHistory a} {bUnary : UnaryHistory b}
    {gUnary : UnaryHistory g} {x y : BHist × BHist} :
    NatBezoutEquation a b g x y ->
      NatBezoutIntegerEquation a b g aUnary bUnary gUnary
        (pairToInt x) (pairToInt y) := by
  intro pairEq
  unfold NatBezoutIntegerEquation
  unfold IntEq IntAdd IntMul
  have xCarrier : IntPairCarrier x.1 x.2 := pairEq.left
  have yCarrier : IntPairCarrier y.1 y.2 := pairEq.right.left
  have xClassifier : IntPairClassifier (intToPair (pairToInt x)) x :=
    intToPair_pairToInt_classifier x xCarrier
  have yClassifier : IntPairClassifier (intToPair (pairToInt y)) y :=
    intToPair_pairToInt_classifier y yCarrier
  have leftNatClassifier :
      IntPairClassifier (intToPair (intOfNat a aUnary)) (a, BHist.Empty) :=
    IntPairClassifier_equivalence_fields.right.right.left ⟨aUnary, unary_empty⟩
  have rightNatClassifier :
      IntPairClassifier (intToPair (intOfNat b bUnary)) (b, BHist.Empty) :=
    IntPairClassifier_equivalence_fields.right.right.left ⟨bUnary, unary_empty⟩
  have gClassifier :
      IntPairClassifier (intToPair (intOfNat g gUnary)) (g, BHist.Empty) :=
    IntPairClassifier_equivalence_fields.right.right.left ⟨gUnary, unary_empty⟩
  have leftMulOuter := intMul_pair_classifier (pairToInt x) (intOfNat a aUnary)
  have leftMulTransport :
      IntPairClassifier
        (pairMul (intToPair (pairToInt x)) (intToPair (intOfNat a aUnary)))
        (pairMul x (a, BHist.Empty)) :=
    pairMul_classifier_congr xClassifier leftNatClassifier
  have leftTerm :
      IntPairClassifier
        (intToPair (intMul (pairToInt x) (intOfNat a aUnary)))
        (pairMul x (a, BHist.Empty)) :=
    IntPairClassifier_trans_pair leftMulOuter leftMulTransport
  have rightMulOuter := intMul_pair_classifier (pairToInt y) (intOfNat b bUnary)
  have rightMulTransport :
      IntPairClassifier
        (pairMul (intToPair (pairToInt y)) (intToPair (intOfNat b bUnary)))
        (pairMul y (b, BHist.Empty)) :=
    pairMul_classifier_congr yClassifier rightNatClassifier
  have rightTerm :
      IntPairClassifier
        (intToPair (intMul (pairToInt y) (intOfNat b bUnary)))
        (pairMul y (b, BHist.Empty)) :=
    IntPairClassifier_trans_pair rightMulOuter rightMulTransport
  have addOuter :=
    intAdd_pair_classifier
      (intMul (pairToInt x) (intOfNat a aUnary))
      (intMul (pairToInt y) (intOfNat b bUnary))
  have addTransport :
      IntPairClassifier
        (pairAdd
          (intToPair (intMul (pairToInt x) (intOfNat a aUnary)))
          (intToPair (intMul (pairToInt y) (intOfNat b bUnary))))
        (pairAdd (pairMul x (a, BHist.Empty)) (pairMul y (b, BHist.Empty))) :=
    pairAdd_classifier_congr leftTerm rightTerm
  exact IntPairClassifier_trans_pair addOuter
    (IntPairClassifier_trans_pair addTransport
      (IntPairClassifier_trans_pair pairEq.right.right
        (IntPairClassifier_equivalence_fields.right.right.right.left gClassifier)))

theorem NatBezoutInteger_natGcdFn {a b : BHist} :
    (aUnary : UnaryHistory a) -> (bUnary : UnaryHistory b) ->
      NatBezoutIntegerEquation a b (natGcdFn a b) aUnary bUnary
        (NatGcd_result_unary (natGcdFn_spec aUnary bUnary))
        (natBezoutIntegerX a b) (natBezoutIntegerY a b) := by
  intro aUnary bUnary
  exact NatBezoutIntegerEquation_of_pair (natBezoutFn_spec aUnary bUnary)

theorem NatBezout {a b : BHist} :
    (aUnary : UnaryHistory a) -> (bUnary : UnaryHistory b) ->
      ∃ x : IntegerUp, ∃ y : IntegerUp,
        NatBezoutIntegerEquation a b (natGcdFn a b) aUnary bUnary
          (NatGcd_result_unary (natGcdFn_spec aUnary bUnary)) x y := by
  intro aUnary bUnary
  exact ⟨natBezoutIntegerX a b, natBezoutIntegerY a b,
    NatBezoutInteger_natGcdFn aUnary bUnary⟩

end BEDC.Derived.GcdUp
