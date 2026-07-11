import BEDC.Derived.RHRoute.EulerHasseEta
import BEDC.Derived.IntUp.UnaryIntMulBridge
import BEDC.Derived.IntUp.UnaryIntOrderBridge
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace BEDC.Derived.RHRoute.EulerHasseEtaCenterProduct

open BEDC.Derived.RHRoute.EulerHasseEta
open BEDC.Derived.IntUp (pairAdd pairNeg pairAdd_carrier pairNeg_carrier)
open BEDC.Derived.IntUp.UnaryIntBridge
  (intEncode intEncode_pairAdd intEncode_eq_core intPairAddEncode)
open BEDC.Derived.IntUp.UnaryIntOrderBridge (intEncode_pairNeg)
open BEDC.Derived.RationalUp
  (intToRat ratZero ratAdd ratMul ratNeg ratLe ratDenInt)

abbrev Rat : Type :=
  BEDC.Derived.RHRoute.EulerHasseEta.Rat

def ratNumEnc (x : Rat) : Int :=
  intEncode (BEDC.Derived.RationalUp.intToPair x.num)

def ratDenEnc (x : Rat) : Int :=
  intEncode (BEDC.Derived.RationalUp.intToPair (ratDenInt x))

theorem unaryLength_intNatToUnary (n : Nat) :
    BEDC.Derived.NatUp.UnaryNatBridge.unaryLength
      (BEDC.Derived.IntUp.natToUnary n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change BEDC.Derived.NatUp.UnaryNatBridge.unaryLength
        (BEDC.FKernel.Hist.BHist.e1 (BEDC.Derived.IntUp.natToUnary n)) =
          Nat.succ n
      change BEDC.Derived.NatUp.UnaryNatBridge.unaryLength
        (BEDC.Derived.IntUp.natToUnary n) + 1 = Nat.succ n
      rw [ih]

theorem intEncode_intOfLeanInt (n : Int) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (BEDC.Derived.BernoulliUp.intOfLeanInt n)) = n := by
  cases n with
  | ofNat m =>
      unfold BEDC.Derived.BernoulliUp.intOfLeanInt
      unfold BEDC.Derived.RationalUp.intToPair
      unfold BEDC.Derived.IntUp.UnaryIntBridge.intEncode
      rw [unaryLength_intNatToUnary]
      rfl
  | negSucc m =>
      unfold BEDC.Derived.BernoulliUp.intOfLeanInt
      unfold BEDC.Derived.RationalUp.intToPair
      unfold BEDC.Derived.IntUp.UnaryIntBridge.intEncode
      rw [unaryLength_intNatToUnary]
      rfl

theorem intEncode_intOfNat (n : Nat)
    (hn : BEDC.FKernel.Unary.UnaryHistory (BEDC.Derived.IntUp.natToUnary n)) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (BEDC.Derived.RationalUp.intOfNat (BEDC.Derived.IntUp.natToUnary n) hn)) =
      Int.ofNat n := by
  unfold BEDC.Derived.RationalUp.intOfNat
  unfold BEDC.Derived.RationalUp.intToPair
  unfold BEDC.Derived.IntUp.UnaryIntBridge.intEncode
  rw [unaryLength_intNatToUnary]
  rfl

theorem rawRatToRat_num_encode (num : Int) (denMinusOne : Nat) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (BEDC.Derived.BernoulliUp.rawRatToRat
          { num := num, denMinusOne := denMinusOne }).num) = num := by
  unfold BEDC.Derived.BernoulliUp.rawRatToRat
  exact intEncode_intOfLeanInt num

theorem rawRatToRat_den_encode (num : Int) (denMinusOne : Nat) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (ratDenInt
          (BEDC.Derived.BernoulliUp.rawRatToRat
            { num := num, denMinusOne := denMinusOne }))) =
      Int.ofNat (Nat.succ denMinusOne) := by
  unfold BEDC.Derived.RationalUp.ratDenInt
  unfold BEDC.Derived.BernoulliUp.rawRatToRat
  exact intEncode_intOfNat (Nat.succ denMinusOne)
    (BEDC.Derived.RationalUp.ratDenCarrier
      { num := BEDC.Derived.BernoulliUp.intOfLeanInt num,
        den := BEDC.Derived.IntUp.natToUnary (Nat.succ denMinusOne),
        den_pos := BEDC.Derived.BernoulliUp.denPosOfMinusOne denMinusOne })

theorem intEncode_IntMul (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (BEDC.Derived.RationalUp.IntMul a b)) =
      intEncode (BEDC.Derived.RationalUp.intToPair a) *
      intEncode (BEDC.Derived.RationalUp.intToPair b) := by
  unfold BEDC.Derived.RationalUp.IntMul
  exact Eq.trans
    (BEDC.Derived.IntUp.UnaryIntBridge.intEncode_classifier
      (BEDC.Derived.RationalUp.intMul_pair_classifier a b))
    (BEDC.Derived.IntUp.UnaryIntMulBridge.intEncode_pairMul
      (BEDC.Derived.RationalUp.intToPair a)
      (BEDC.Derived.RationalUp.intToPair b)
      (BEDC.Derived.RationalUp.intToPair_carrier a)
      (BEDC.Derived.RationalUp.intToPair_carrier b))

theorem intEncode_intMul (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    intEncode
      (BEDC.Derived.RationalUp.intToPair
        (BEDC.Derived.RationalUp.intMul a b)) =
      intEncode (BEDC.Derived.RationalUp.intToPair a) *
      intEncode (BEDC.Derived.RationalUp.intToPair b) := by
  exact intEncode_IntMul a b

private theorem subNatNat_succ_succ_local (m n : Nat) :
    Int.subNatNat (m + 1) (n + 1) = Int.subNatNat m n := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_sub_succ_eq_sub]

private theorem subNatNat_zero_right_local : ∀ m : Nat,
    Int.subNatNat m 0 = Int.ofNat m
  | 0 => rfl
  | m + 1 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]

private theorem subNatNat_zero_left_local : ∀ n : Nat,
    Int.subNatNat 0 n = Int.negOfNat n
  | 0 => rfl
  | _ + 1 => rfl

private theorem int_zero_add_local : ∀ z : Int, (0 : Int) + z = z
  | Int.ofNat n => by
      change Int.ofNat (0 + n) = Int.ofNat n
      rw [Nat.zero_add]
  | Int.negSucc _ => rfl

private theorem int_add_zero_local : ∀ z : Int, z + (0 : Int) = z
  | Int.ofNat n => by
      change Int.ofNat (n + 0) = Int.ofNat n
      rw [Nat.add_zero]
  | Int.negSucc _ => rfl

private theorem ofNat_add_subNatNat_local : ∀ a c d : Nat,
    Int.ofNat a + Int.subNatNat c d = Int.subNatNat (a + c) d
  | a, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_local a]
      exact int_add_zero_local (Int.ofNat a)
  | a, c + 1, 0 => by
      rw [subNatNat_zero_right_local (c + 1)]
      rw [subNatNat_zero_right_local (a + (c + 1))]
      exact Int.ofNat_add_ofNat a (c + 1)
  | a, 0, d + 1 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_local (d + 1)]
      rfl
  | a, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_local c d]
      rw [Nat.add_succ]
      rw [subNatNat_succ_succ_local (a + c) d]
      exact ofNat_add_subNatNat_local a c d

private theorem negOfNat_add_subNatNat_local : ∀ b c d : Nat,
    Int.negOfNat b + Int.subNatNat c d = Int.subNatNat c (b + d)
  | 0, c, d => by
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_local (Int.subNatNat c d)
  | b + 1, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_local (b + 1)]
      exact int_add_zero_local (Int.negOfNat (b + 1))
  | b + 1, c + 1, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_local (c + 1)]
      rfl
  | b + 1, 0, d + 1 => by
      rw [subNatNat_zero_left_local (b + 1 + (d + 1))]
      rw [subNatNat_zero_left_local (d + 1)]
      rw [Nat.add_succ]
      exact Int.negOfNat_add (b + 1) (d + 1)
  | b + 1, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_local c d]
      rw [Nat.add_succ]
      change Int.negOfNat (b + 1) + Int.subNatNat c d =
        Int.subNatNat (c + 1) ((b + 1 + d) + 1)
      rw [subNatNat_succ_succ_local c (b + 1 + d)]
      exact negOfNat_add_subNatNat_local (b + 1) c d

private theorem subNatNat_add_subNatNat_local : ∀ a b c d : Nat,
    Int.subNatNat a b + Int.subNatNat c d =
      Int.subNatNat (a + c) (b + d)
  | 0, 0, c, d => by
      rw [Nat.zero_add]
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_local (Int.subNatNat c d)
  | a + 1, 0, c, d => by
      rw [subNatNat_zero_right_local (a + 1)]
      rw [Nat.zero_add]
      exact ofNat_add_subNatNat_local (a + 1) c d
  | 0, b + 1, c, d => by
      rw [subNatNat_zero_left_local (b + 1)]
      rw [Nat.zero_add]
      exact negOfNat_add_subNatNat_local (b + 1) c d
  | a + 1, b + 1, c, d => by
      rw [subNatNat_succ_succ_local a b]
      rw [Nat.succ_add]
      rw [Nat.succ_add]
      rw [subNatNat_succ_succ_local (a + c) (b + d)]
      exact subNatNat_add_subNatNat_local a b c d

theorem intEncode_pairAdd_eq_add (x y : BEDC.FKernel.Hist.BHist × BEDC.FKernel.Hist.BHist) :
    intEncode (pairAdd x y) = intEncode x + intEncode y := by
  rw [intEncode_pairAdd]
  rw [intEncode_eq_core x]
  rw [intEncode_eq_core y]
  unfold intPairAddEncode BEDC.Derived.IntUp.UnaryIntBridge.intEncodeCore
  exact (subNatNat_add_subNatNat_local
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength x.1)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength x.2)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength y.1)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength y.2)).symm

theorem intEncode_intAdd (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    intEncode (BEDC.Derived.RationalUp.intToPair
      (BEDC.Derived.RationalUp.intAdd a b)) =
      intEncode (BEDC.Derived.RationalUp.intToPair a) +
        intEncode (BEDC.Derived.RationalUp.intToPair b) := by
  unfold BEDC.Derived.RationalUp.intAdd
  exact Eq.trans
    (BEDC.Derived.IntUp.UnaryIntBridge.intEncode_classifier
      (BEDC.Derived.RationalUp.intToPair_pairToInt_classifier _
        (pairAdd_carrier
          (BEDC.Derived.RationalUp.intToPair_carrier a)
          (BEDC.Derived.RationalUp.intToPair_carrier b))))
    (intEncode_pairAdd_eq_add
      (BEDC.Derived.RationalUp.intToPair a)
      (BEDC.Derived.RationalUp.intToPair b))

theorem intEncode_IntAdd (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    intEncode (BEDC.Derived.RationalUp.intToPair
      (BEDC.Derived.RationalUp.IntAdd a b)) =
      intEncode (BEDC.Derived.RationalUp.intToPair a) +
        intEncode (BEDC.Derived.RationalUp.intToPair b) := by
  unfold BEDC.Derived.RationalUp.IntAdd
  exact intEncode_intAdd a b

theorem intEncode_IntNeg (a : BEDC.Derived.PrimeUp.IntegerUp) :
    intEncode (BEDC.Derived.RationalUp.intToPair
      (BEDC.Derived.RationalUp.IntNeg a)) =
      -intEncode (BEDC.Derived.RationalUp.intToPair a) := by
  unfold BEDC.Derived.RationalUp.IntNeg BEDC.Derived.RationalUp.intNeg
  exact Eq.trans
    (BEDC.Derived.IntUp.UnaryIntBridge.intEncode_classifier
      (BEDC.Derived.RationalUp.intToPair_pairToInt_classifier _
        (pairNeg_carrier (BEDC.Derived.RationalUp.intToPair_carrier a))))
    (intEncode_pairNeg (BEDC.Derived.RationalUp.intToPair a))

theorem rawRatLe_sound_of_cross
    (leftNum : Int) (leftDen : Nat) (rightNum : Int) (rightDen : Nat)
    (denLeft_pos : 0 < leftDen) (denRight_pos : 0 < rightDen)
    (cross_le : leftNum * Int.ofNat rightDen <= rightNum * Int.ofNat leftDen) :
    ratLe (q leftNum leftDen) (q rightNum rightDen) := by
  cases leftDen with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ denLeft_pos)
  | succ leftPred =>
      cases rightDen with
      | zero =>
          exact False.elim (Nat.not_lt_zero _ denRight_pos)
      | succ rightPred =>
          unfold q BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat
          change BEDC.Derived.RationalUp.intLe
            (BEDC.Derived.RationalUp.IntMul
              (BEDC.Derived.BernoulliUp.rawRatToRat
                { num := leftNum, denMinusOne := leftPred }).num
              (ratDenInt
                (BEDC.Derived.BernoulliUp.rawRatToRat
                  { num := rightNum, denMinusOne := rightPred })))
            (BEDC.Derived.RationalUp.IntMul
              (BEDC.Derived.BernoulliUp.rawRatToRat
                { num := rightNum, denMinusOne := rightPred }).num
              (ratDenInt
                (BEDC.Derived.BernoulliUp.rawRatToRat
                  { num := leftNum, denMinusOne := leftPred })))
          apply (BEDC.Derived.IntUp.UnaryIntOrderBridge.intEncode_le
            (BEDC.Derived.RationalUp.intToPair_carrier _)
            (BEDC.Derived.RationalUp.intToPair_carrier _)).mpr
          rw [intEncode_IntMul, intEncode_IntMul]
          rw [rawRatToRat_num_encode, rawRatToRat_num_encode]
          rw [rawRatToRat_den_encode, rawRatToRat_den_encode]
          exact cross_le

theorem rawRatLeCert_sound (cert : RawRatLeCert) :
    ratLe (q cert.leftNum cert.leftDen) (q cert.rightNum cert.rightDen) := by
  exact rawRatLe_sound_of_cross cert.leftNum cert.leftDen cert.rightNum cert.rightDen
    cert.denLeft_pos cert.denRight_pos cert.cross_le

theorem ratNumEnc_q_of_pos (num : Int) (den : Nat) (hden : 0 < den) :
    ratNumEnc (q num den) = num := by
  cases den with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hden)
  | succ denPred =>
      unfold ratNumEnc q BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat
      exact rawRatToRat_num_encode num denPred

theorem ratDenEnc_q_of_pos (num : Int) (den : Nat) (hden : 0 < den) :
    ratDenEnc (q num den) = Int.ofNat den := by
  cases den with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hden)
  | succ denPred =>
      unfold ratDenEnc q BEDC.Derived.RHRoute.ZetaDerivativeBox.ratOfIntOverNat
      exact rawRatToRat_den_encode num denPred

theorem ratNumEnc_q_zero_one :
    ratNumEnc (q 0 1) = 0 :=
  ratNumEnc_q_of_pos 0 1 (by decide)

theorem ratDenEnc_q_zero_one :
    ratDenEnc (q 0 1) = 1 :=
  ratDenEnc_q_of_pos 0 1 (by decide)

theorem ratNumEnc_q_neg_two_million :
    ratNumEnc (q (-2) 1000000) = -2 :=
  ratNumEnc_q_of_pos (-2) 1000000 (by decide)

theorem ratDenEnc_q_neg_two_million :
    ratDenEnc (q (-2) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-2) 1000000 (by decide)

theorem ratNumEnc_q_neg_three_million :
    ratNumEnc (q (-3) 1000000) = -3 :=
  ratNumEnc_q_of_pos (-3) 1000000 (by decide)

theorem ratDenEnc_q_neg_three_million :
    ratDenEnc (q (-3) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-3) 1000000 (by decide)

theorem ratNumEnc_q_neg_fortyseven_million :
    ratNumEnc (q (-47) 1000000) = -47 :=
  ratNumEnc_q_of_pos (-47) 1000000 (by decide)

theorem ratDenEnc_q_neg_fortyseven_million :
    ratDenEnc (q (-47) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-47) 1000000 (by decide)

theorem ratNumEnc_q_neg_fortyeight_million :
    ratNumEnc (q (-48) 1000000) = -48 :=
  ratNumEnc_q_of_pos (-48) 1000000 (by decide)

theorem ratDenEnc_q_neg_fortyeight_million :
    ratDenEnc (q (-48) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-48) 1000000 (by decide)

theorem ratNumEnc_q_three_million :
    ratNumEnc (q 3 1000000) = 3 :=
  ratNumEnc_q_of_pos 3 1000000 (by decide)

theorem ratDenEnc_q_three_million :
    ratDenEnc (q 3 1000000) = 1000000 :=
  ratDenEnc_q_of_pos 3 1000000 (by decide)

theorem ratNumEnc_q_four_million :
    ratNumEnc (q 4 1000000) = 4 :=
  ratNumEnc_q_of_pos 4 1000000 (by decide)

theorem ratDenEnc_q_four_million :
    ratDenEnc (q 4 1000000) = 1000000 :=
  ratDenEnc_q_of_pos 4 1000000 (by decide)

theorem ratNumEnc_q_neg_twentyone_million :
    ratNumEnc (q (-21) 1000000) = -21 :=
  ratNumEnc_q_of_pos (-21) 1000000 (by decide)

theorem ratDenEnc_q_neg_twentyone_million :
    ratDenEnc (q (-21) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-21) 1000000 (by decide)

theorem ratNumEnc_q_neg_nineteen_million :
    ratNumEnc (q (-19) 1000000) = -19 :=
  ratNumEnc_q_of_pos (-19) 1000000 (by decide)

theorem ratDenEnc_q_neg_nineteen_million :
    ratDenEnc (q (-19) 1000000) = 1000000 :=
  ratDenEnc_q_of_pos (-19) 1000000 (by decide)

theorem ratNumEnc_q_257_625 :
    ratNumEnc (q 257 625) = 257 :=
  ratNumEnc_q_of_pos 257 625 (by decide)

theorem ratDenEnc_q_257_625 :
    ratDenEnc (q 257 625) = 625 :=
  ratDenEnc_q_of_pos 257 625 (by decide)

theorem ratNumEnc_q_4113_10000 :
    ratNumEnc (q 4113 10000) = 4113 :=
  ratNumEnc_q_of_pos 4113 10000 (by decide)

theorem ratDenEnc_q_4113_10000 :
    ratDenEnc (q 4113 10000) = 10000 :=
  ratDenEnc_q_of_pos 4113 10000 (by decide)

theorem ratNumEnc_q_913_10000 :
    ratNumEnc (q 913 10000) = 913 :=
  ratNumEnc_q_of_pos 913 10000 (by decide)

theorem ratDenEnc_q_913_10000 :
    ratDenEnc (q 913 10000) = 10000 :=
  ratDenEnc_q_of_pos 913 10000 (by decide)

theorem ratNumEnc_q_183_2000 :
    ratNumEnc (q 183 2000) = 183 :=
  ratNumEnc_q_of_pos 183 2000 (by decide)

theorem ratDenEnc_q_183_2000 :
    ratDenEnc (q 183 2000) = 2000 :=
  ratDenEnc_q_of_pos 183 2000 (by decide)

theorem ratNumEnc_mul (x y : Rat) :
    ratNumEnc (ratMul x y) = ratNumEnc x * ratNumEnc y := by
  unfold ratNumEnc ratMul
  exact intEncode_IntMul x.num y.num

theorem ratDenEnc_mul (x y : Rat) :
    ratDenEnc (ratMul x y) = ratDenEnc x * ratDenEnc y := by
  unfold ratDenEnc
  exact Eq.trans
    (BEDC.Derived.IntUp.UnaryIntBridge.intEncode_classifier
      (BEDC.Derived.RationalUp.ratDenInt_mul x y))
    (intEncode_IntMul (ratDenInt x) (ratDenInt y))

theorem ratNumEnc_neg (x : Rat) :
    ratNumEnc (ratNeg x) = -ratNumEnc x := by
  unfold ratNumEnc ratNeg
  exact intEncode_IntNeg x.num

theorem ratDenEnc_neg (x : Rat) :
    ratDenEnc (ratNeg x) = ratDenEnc x := by
  rfl

theorem ratNumEnc_add (x y : Rat) :
    ratNumEnc (ratAdd x y) =
      ratNumEnc x * ratDenEnc y + ratNumEnc y * ratDenEnc x := by
  unfold ratNumEnc ratDenEnc ratAdd BEDC.Derived.RationalUp.ratDenInt
  rw [intEncode_intAdd, intEncode_intMul, intEncode_intMul]

theorem ratDenEnc_add (x y : Rat) :
    ratDenEnc (ratAdd x y) = ratDenEnc x * ratDenEnc y := by
  unfold ratDenEnc
  exact Eq.trans
    (BEDC.Derived.IntUp.UnaryIntBridge.intEncode_classifier
      (BEDC.Derived.RationalUp.ratDenInt_add x y))
    (intEncode_IntMul (ratDenInt x) (ratDenInt y))

theorem ratLe_of_enc_cross {x y : Rat}
    (h : ratNumEnc x * ratDenEnc y <= ratNumEnc y * ratDenEnc x) :
    ratLe x y := by
  unfold ratLe BEDC.Derived.RationalUp.intLe
  apply (BEDC.Derived.IntUp.UnaryIntOrderBridge.intEncode_le
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)).mpr
  rw [intEncode_IntMul, intEncode_IntMul]
  exact h

macro "rat_enc_decide" : tactic =>
  `(tactic|
    (apply ratLe_of_enc_cross
     simp only [ratNumEnc_add, ratDenEnc_add, ratNumEnc_mul, ratDenEnc_mul,
       ratNumEnc_neg, ratDenEnc_neg,
       ratNumEnc_q_zero_one, ratDenEnc_q_zero_one,
       ratNumEnc_q_neg_two_million, ratDenEnc_q_neg_two_million,
       ratNumEnc_q_neg_three_million, ratDenEnc_q_neg_three_million,
       ratNumEnc_q_neg_fortyseven_million, ratDenEnc_q_neg_fortyseven_million,
       ratNumEnc_q_neg_fortyeight_million, ratDenEnc_q_neg_fortyeight_million,
       ratNumEnc_q_three_million, ratDenEnc_q_three_million,
       ratNumEnc_q_four_million, ratDenEnc_q_four_million,
       ratNumEnc_q_neg_twentyone_million, ratDenEnc_q_neg_twentyone_million,
       ratNumEnc_q_neg_nineteen_million, ratDenEnc_q_neg_nineteen_million,
       ratNumEnc_q_257_625, ratDenEnc_q_257_625,
       ratNumEnc_q_4113_10000, ratDenEnc_q_4113_10000,
       ratNumEnc_q_913_10000, ratDenEnc_q_913_10000,
       ratNumEnc_q_183_2000, ratDenEnc_q_183_2000]
     decide))

theorem etaCBox_re_hi_nonpos :
    ratLe (q (-2) 1000000) (q 0 1) := by
  rat_enc_decide

theorem etaCBox_im_hi_nonpos :
    ratLe (q (-47) 1000000) (q 0 1) := by
  rat_enc_decide

theorem invDBoxC_re_lo_nonneg :
    ratLe (q 0 1) (q 257 625) := by
  rat_enc_decide

theorem invDBoxC_re_hi_nonneg :
    ratLe (q 0 1) (q 4113 10000) := by
  rat_enc_decide

theorem invDBoxC_im_lo_nonneg :
    ratLe (q 0 1) (q 913 10000) := by
  rat_enc_decide

theorem invDBoxC_im_hi_nonneg :
    ratLe (q 0 1) (q 183 2000) := by
  rat_enc_decide

theorem centerProduct_re_lower_fits :
    ratLe (q 3 1000000)
    (ratAdd (ratMul (q (-3) 1000000) (q 4113 10000))
      (ratNeg (ratMul (q (-47) 1000000) (q 913 10000)))) := by
  rat_enc_decide

theorem centerProduct_re_upper_fits :
    ratLe
    (ratAdd (ratMul (q (-2) 1000000) (q 257 625))
      (ratNeg (ratMul (q (-48) 1000000) (q 183 2000))))
    (q 4 1000000) := by
  rat_enc_decide

theorem centerProduct_im_lower_fits :
    ratLe (q (-21) 1000000)
    (ratAdd (ratMul (q (-3) 1000000) (q 183 2000))
      (ratMul (q (-48) 1000000) (q 4113 10000))) := by
  rat_enc_decide

theorem centerProduct_im_upper_fits :
    ratLe
    (ratAdd (ratMul (q (-2) 1000000) (q 913 10000))
      (ratMul (q (-47) 1000000) (q 257 625)))
    (q (-19) 1000000) := by
  rat_enc_decide

end BEDC.Derived.RHRoute.EulerHasseEtaCenterProduct
