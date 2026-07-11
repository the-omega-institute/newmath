import BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly
import BEDC.Derived.IntUp.UnaryIntMulBridge
import BEDC.Derived.IntUp.UnaryIntOrderBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.IntUp.UnaryIntBridge
open BEDC.Derived.IntUp.UnaryIntMulBridge
open BEDC.Derived.IntUp.UnaryIntOrderBridge
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel

def qValid (x : QRat) : Prop :=
  0 < x.den

def ratOfNat (n : Nat) : BRat :=
  intToRat (intToBEDC (Int.ofNat n))

def ratInvNat (n : Nat) : BRat :=
  qToBRat (qraw 1 n)

def evalB : Poly -> BRat -> BRat
  | [], _ => ratZero
  | a :: rest, x => ratAdd (qToBRat a) (ratMul x (evalB rest x))

def antiderivBFrom (n : Nat) : Poly -> List BRat
  | [] => []
  | a :: rest => ratMul (qToBRat a) (ratInvNat n) :: antiderivBFrom (n + 1) rest

def antiderivB (p : Poly) : List BRat :=
  ratZero :: antiderivBFrom 1 p

def evalBRats : List BRat -> BRat -> BRat
  | [], _ => ratZero
  | a :: rest, x => ratAdd a (ratMul x (evalBRats rest x))

def polyValid : Poly -> Prop
  | [] => True
  | a :: rest => qValid a ∧ polyValid rest

private theorem qValid_tail {a : QRat} {p : Poly} :
    polyValid (a :: p) -> polyValid p := by
  intro h
  exact h.right

private theorem qValid_head {a : QRat} {p : Poly} :
    polyValid (a :: p) -> qValid a := by
  intro h
  exact h.left

private theorem intToPair_intToBEDC_carrier (z : Int) :
    IntPairCarrier (intToPair (intToBEDC z)).1 (intToPair (intToBEDC z)).2 :=
  intToPair_carrier _

private theorem unaryLength_intNatToUnary (n : Nat) :
    BEDC.Derived.NatUp.UnaryNatBridge.unaryLength
      (BEDC.Derived.IntUp.natToUnary n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        BEDC.Derived.NatUp.UnaryNatBridge.unaryLength
          (BHist.e1 (BEDC.Derived.IntUp.natToUnary n)) = Nat.succ n
      exact congrArg (fun k => k + 1) ih

private theorem bedcIntValue_intToBEDC (z : Int) :
    intEncode (intToPair (intToBEDC z)) = z := by
  cases z with
  | ofNat n =>
      change intEncode (natToUnary n, BHist.Empty) = Int.ofNat n
      unfold intEncode
      rw [unaryLength_intNatToUnary]
      change (Int.ofNat n - Int.ofNat 0) = Int.ofNat n
      cases n <;> rfl
  | negSucc n =>
      change intEncode (BHist.Empty, natToUnary (Nat.succ n)) = Int.negSucc n
      unfold intEncode
      rw [unaryLength_intNatToUnary]
      change (Int.ofNat 0 - Int.ofNat (Nat.succ n)) = Int.negSucc n
      rfl

private theorem IntPairClassifier_of_intEncode_eq {x y : BHist × BHist}
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    intEncode x = intEncode y -> IntPairClassifier x y := by
  intro h
  have xxLe : pairLe x x := pairLe_of_length_order hx hx (Nat.le_refl _)
  have yyLe : pairLe y y := pairLe_of_length_order hy hy (Nat.le_refl _)
  have xxEncodeLe : intEncode x ≤ intEncode x := (intEncode_le hx hx).mp xxLe
  have yyEncodeLe : intEncode y ≤ intEncode y := (intEncode_le hy hy).mp yyLe
  have xyLe : pairLe x y := by
    exact (intEncode_le hx hy).mpr (by rw [h]; exact yyEncodeLe)
  have yxLe : pairLe y x := by
    exact (intEncode_le hy hx).mpr (by rw [← h]; exact xxEncodeLe)
  exact pairLe_antisymm_classifier hx hy xyLe yxLe

private theorem IntEq_of_bedcIntValue_eq {x y : BEDC.Derived.PrimeUp.IntegerUp} :
    intEncode (intToPair x) = intEncode (intToPair y) -> IntEq x y := by
  intro h
  exact IntPairClassifier_of_intEncode_eq (intToPair_carrier x) (intToPair_carrier y) h

private theorem intToBEDC_respects {a b : Int} :
    a = b -> IntEq (intToBEDC a) (intToBEDC b) := by
  intro h
  rw [h]
  exact IntEq_refl (intToBEDC b)

private theorem IntPairClassifier_symm_local {x y : BHist × BHist} :
    IntPairClassifier x y -> IntPairClassifier y x := by
  intro h
  exact IntPairClassifier_equivalence_fields.right.right.right.left h

private theorem subNatNat_succ_succ_pure_local (m n : Nat) :
    Int.subNatNat (m + 1) (n + 1) = Int.subNatNat m n := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_sub_succ_eq_sub]

private theorem subNatNat_zero_right_pure_local : ∀ m : Nat,
    Int.subNatNat m 0 = Int.ofNat m
  | 0 => rfl
  | m + 1 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]

private theorem subNatNat_zero_left_pure_local : ∀ n : Nat,
    Int.subNatNat 0 n = Int.negOfNat n
  | 0 => rfl
  | _ + 1 => rfl

private theorem int_zero_add_pure_local : ∀ z : Int, (0 : Int) + z = z
  | Int.ofNat n => by
      change Int.ofNat (0 + n) = Int.ofNat n
      rw [Nat.zero_add]
  | Int.negSucc _ => rfl

private theorem int_add_zero_pure_local : ∀ z : Int, z + (0 : Int) = z
  | Int.ofNat n => by
      change Int.ofNat (n + 0) = Int.ofNat n
      rw [Nat.add_zero]
  | Int.negSucc _ => rfl

private theorem ofNat_add_subNatNat_pure_local : ∀ a c d : Nat,
    Int.ofNat a + Int.subNatNat c d = Int.subNatNat (a + c) d
  | a, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_pure_local a]
      exact int_add_zero_pure_local (Int.ofNat a)
  | a, c + 1, 0 => by
      rw [subNatNat_zero_right_pure_local (c + 1)]
      rw [subNatNat_zero_right_pure_local (a + (c + 1))]
      exact Int.ofNat_add_ofNat a (c + 1)
  | a, 0, d + 1 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_pure_local (d + 1)]
      rfl
  | a, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_pure_local c d]
      rw [Nat.add_succ]
      rw [subNatNat_succ_succ_pure_local (a + c) d]
      exact ofNat_add_subNatNat_pure_local a c d

private theorem negOfNat_add_subNatNat_pure_local : ∀ b c d : Nat,
    Int.negOfNat b + Int.subNatNat c d = Int.subNatNat c (b + d)
  | 0, c, d => by
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_pure_local (Int.subNatNat c d)
  | b + 1, 0, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_left_pure_local (b + 1)]
      exact int_add_zero_pure_local (Int.negOfNat (b + 1))
  | b + 1, c + 1, 0 => by
      rw [Nat.add_zero]
      rw [subNatNat_zero_right_pure_local (c + 1)]
      rfl
  | b + 1, 0, d + 1 => by
      rw [subNatNat_zero_left_pure_local (b + 1 + (d + 1))]
      rw [subNatNat_zero_left_pure_local (d + 1)]
      rw [Nat.add_succ]
      exact Int.negOfNat_add (b + 1) (d + 1)
  | b + 1, c + 1, d + 1 => by
      rw [subNatNat_succ_succ_pure_local c d]
      rw [Nat.add_succ]
      change Int.negOfNat (b + 1) + Int.subNatNat c d =
        Int.subNatNat (c + 1) ((b + 1 + d) + 1)
      rw [subNatNat_succ_succ_pure_local c (b + 1 + d)]
      exact negOfNat_add_subNatNat_pure_local (b + 1) c d

private theorem subNatNat_add_subNatNat_pure_local : ∀ a b c d : Nat,
    Int.subNatNat a b + Int.subNatNat c d =
      Int.subNatNat (a + c) (b + d)
  | 0, 0, c, d => by
      rw [Nat.zero_add]
      rw [Nat.zero_add]
      change (0 : Int) + Int.subNatNat c d = Int.subNatNat c d
      exact int_zero_add_pure_local (Int.subNatNat c d)
  | a + 1, 0, c, d => by
      rw [subNatNat_zero_right_pure_local (a + 1)]
      rw [Nat.zero_add]
      exact ofNat_add_subNatNat_pure_local (a + 1) c d
  | 0, b + 1, c, d => by
      rw [subNatNat_zero_left_pure_local (b + 1)]
      rw [Nat.zero_add]
      exact negOfNat_add_subNatNat_pure_local (b + 1) c d
  | a + 1, b + 1, c, d => by
      rw [subNatNat_succ_succ_pure_local a b]
      rw [Nat.succ_add]
      rw [Nat.succ_add]
      rw [subNatNat_succ_succ_pure_local (a + c) (b + d)]
      exact subNatNat_add_subNatNat_pure_local a b c d

private theorem intEncode_pairAdd_eq_add (x y : BHist × BHist) :
    intEncode (pairAdd x y) = intEncode x + intEncode y := by
  rw [intEncode_pairAdd]
  rw [intEncode_eq_core x]
  rw [intEncode_eq_core y]
  unfold intPairAddEncode intEncodeCore
  exact (subNatNat_add_subNatNat_pure_local
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength x.1)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength x.2)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength y.1)
    (BEDC.Derived.NatUp.UnaryNatBridge.unaryLength y.2)).symm

private theorem intToBEDC_neg (z : Int) :
    IntEq (intToBEDC (-z)) (IntNeg (intToBEDC z)) := by
  unfold IntEq IntNeg intNeg
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          change IntPairClassifier (BHist.Empty, BHist.Empty)
            (intToPair (pairToInt (pairNeg (BHist.Empty, BHist.Empty))))
          exact IntPairClassifier_equivalence_fields.right.right.right.left
            (intToPair_pairToInt_classifier _
              (pairNeg_carrier ⟨unary_empty, unary_empty⟩))
      | succ n =>
          change IntPairClassifier (BHist.Empty, natToUnary (n + 1))
            (intToPair (pairToInt (pairNeg (natToUnary (n + 1), BHist.Empty))))
          exact IntPairClassifier_equivalence_fields.right.right.right.left
            (intToPair_pairToInt_classifier _
              (pairNeg_carrier ⟨natToUnary_unary (n + 1), unary_empty⟩))
  | negSucc n =>
      change IntPairClassifier (natToUnary (n + 1), BHist.Empty)
        (intToPair (pairToInt (pairNeg (BHist.Empty, natToUnary (n + 1)))))
      exact IntPairClassifier_equivalence_fields.right.right.right.left
        (intToPair_pairToInt_classifier _
          (pairNeg_carrier ⟨unary_empty, natToUnary_unary (n + 1)⟩))

private theorem intToBEDC_mul (a b : Int) :
    IntEq (intToBEDC (a * b)) (IntMul (intToBEDC a) (intToBEDC b)) := by
  apply IntEq_of_bedcIntValue_eq
  calc
    intEncode (intToPair (intToBEDC (a * b))) = a * b :=
      bedcIntValue_intToBEDC (a * b)
    _ = intEncode (intToPair (intToBEDC a)) *
        intEncode (intToPair (intToBEDC b)) := by
      rw [bedcIntValue_intToBEDC]
      rw [bedcIntValue_intToBEDC]
    _ = intEncode (pairMul (intToPair (intToBEDC a)) (intToPair (intToBEDC b))) :=
      (intEncode_pairMul _ _
        (intToPair_carrier (intToBEDC a))
        (intToPair_carrier (intToBEDC b))).symm
    _ = intEncode (intToPair (IntMul (intToBEDC a) (intToBEDC b))) := by
      unfold IntMul
      exact (intEncode_classifier
        (intMul_pair_classifier (intToBEDC a) (intToBEDC b))).symm

private theorem intToBEDC_add (a b : Int) :
    IntEq (intToBEDC (a + b)) (IntAdd (intToBEDC a) (intToBEDC b)) := by
  apply IntEq_of_bedcIntValue_eq
  calc
    intEncode (intToPair (intToBEDC (a + b))) = a + b :=
      bedcIntValue_intToBEDC (a + b)
    _ = intEncode (intToPair (intToBEDC a)) +
        intEncode (intToPair (intToBEDC b)) := by
      rw [bedcIntValue_intToBEDC]
      rw [bedcIntValue_intToBEDC]
    _ = intEncode (pairAdd (intToPair (intToBEDC a)) (intToPair (intToBEDC b))) := by
      exact (intEncode_pairAdd_eq_add
        (intToPair (intToBEDC a)) (intToPair (intToBEDC b))).symm
    _ = intEncode (intToPair (IntAdd (intToBEDC a) (intToBEDC b))) := by
      unfold IntAdd intAdd
      exact (intEncode_classifier
        (intAdd_pair_classifier (intToBEDC a) (intToBEDC b))).symm

private theorem natToUnary_pos_den_bridge {n : Nat} (h : 0 < n) :
    NatUnaryStrictPrefix NatOne (natToUnary n) ∨ hsame (natToUnary n) NatOne := by
  cases n with
  | zero => cases h
  | succ n =>
      cases n with
      | zero => exact Or.inr rfl
      | succ n =>
          apply Or.inl
          apply NatUnaryStrictPrefix_of_length_lt
          · exact unary_e1_closed unary_empty
          · exact BEDC.Derived.IntUp.natToUnary_unary (Nat.succ (Nat.succ n))
          · rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
            rw [BEDC.Derived.IntUp.natToUnary_length]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

def rawBRat (num : Int) (den : Nat) (hden : 0 < den) : BRat :=
  { num := intToBEDC num
    den := natToUnary den
    den_pos := natToUnary_pos_den_bridge hden }

private theorem qToBRat_valid_eq_raw (x : QRat) (hx : qValid x) :
    qToBRat x = rawBRat x.num x.den hx := by
  cases x with
  | mk num den =>
      unfold qValid at hx
      cases den with
      | zero => cases hx
      | succ d => rfl

theorem qToBRat_qzero :
    RatEq (qToBRat qzero) ratZero := by
  exact RatEq_refl ratZero

theorem qToBRat_qone :
    RatEq (qToBRat qone) ratOne := by
  exact RatEq_refl ratOne

theorem qToBRat_qOfNat (n : Nat) :
    RatEq (qToBRat (qOfNat n)) (ratOfNat n) := by
  exact RatEq_refl (ratOfNat n)

private theorem nat_mul_pos_local {a b : Nat} :
    0 < a -> 0 < b -> 0 < a * b := by
  intro ha hb
  cases a with
  | zero => cases ha
  | succ a =>
      cases b with
      | zero => cases hb
      | succ b => exact Nat.succ_pos _

theorem qToBRat_qneg (x : QRat) :
    RatEq (qToBRat (qneg x)) (ratNeg (qToBRat x)) := by
  cases x with
  | mk num den =>
      cases den with
      | zero =>
          unfold qneg qToBRat
          exact RatEq_symm (ratNeg_respects qToBRat_qzero)
      | succ d =>
          apply ratEq_of_num_den_intEq
          · unfold qneg qToBRat ratNeg
            exact intToBEDC_neg num
          · unfold qneg qToBRat ratNeg ratDenInt
            exact IntEq_refl _

private theorem intToBEDC_nat_mul (a b : Nat) :
    IntEq (intToBEDC (Int.ofNat (a * b)))
      (IntMul (intToBEDC (Int.ofNat a)) (intToBEDC (Int.ofNat b))) := by
  exact intToBEDC_mul (Int.ofNat a) (Int.ofNat b)

private theorem denInt_raw (num : Int) (den : Nat) (hden : 0 < den) :
    IntEq (ratDenInt (rawBRat num den hden)) (intToBEDC (Int.ofNat den)) := by
  unfold rawBRat ratDenInt
  exact IntEq_refl _

private theorem ratEq_raw_of_cross {an bn : Int} {ad bd : Nat}
    (had : 0 < ad) (hbd : 0 < bd) :
    an * Int.ofNat bd = bn * Int.ofNat ad ->
      RatEq (rawBRat an ad had) (rawBRat bn bd hbd) := by
  intro hcross
  let x := rawBRat an ad had
  let y := rawBRat bn bd hbd
  change IntEq (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x))
  have yden : IntEq (ratDenInt y) (intToBEDC (Int.ofNat bd)) := by
    unfold y
    exact denInt_raw bn bd hbd
  have xden : IntEq (ratDenInt x) (intToBEDC (Int.ofNat ad)) := by
    unfold x
    exact denInt_raw an ad had
  have middle :
      IntEq
        (IntMul (intToBEDC an) (intToBEDC (Int.ofNat bd)))
        (IntMul (intToBEDC bn) (intToBEDC (Int.ofNat ad))) :=
    IntEq_trans (IntEq_symm (intToBEDC_mul an (Int.ofNat bd)))
      (IntEq_trans (intToBEDC_respects hcross)
        (intToBEDC_mul bn (Int.ofNat ad)))
  exact IntEq_trans (intMul_left_congr yden)
    (IntEq_trans middle (IntEq_symm (intMul_left_congr xden)))

def qrawAdd (x y : QRat) : QRat :=
  qraw (x.num * Int.ofNat y.den + y.num * Int.ofNat x.den) (x.den * y.den)

def qrawSub (x y : QRat) : QRat :=
  qrawAdd x (qneg y)

def qrawMul (x y : QRat) : QRat :=
  qraw (x.num * y.num) (x.den * y.den)

def qrawDivNat (x : QRat) (n : Nat) : QRat :=
  qraw x.num (x.den * n)

def evalRaw : Poly -> QRat -> QRat
  | [], _ => qzero
  | a :: rest, x => qrawAdd a (qrawMul x (evalRaw rest x))

def antiderivRawFrom (n : Nat) : Poly -> Poly
  | [] => []
  | a :: rest => qrawDivNat a n :: antiderivRawFrom (n + 1) rest

def antiderivRaw (p : Poly) : Poly :=
  qzero :: antiderivRawFrom 1 p

def polyValidAfterRawEval (p : Poly) (x : QRat) : Prop :=
  qValid x -> polyValid p -> qValid (evalRaw p x)

def polyValidAfterRawAntiderivFrom (n : Nat) (p : Poly) : Prop :=
  0 < n -> polyValid p -> polyValid (antiderivRawFrom n p)

-- `qnormalize` is built from Lean `Nat.gcd` and `/`. A normalized bridge needs
-- `qToBRat (qnormalize num den) ~ rawBRat num den hden`; the available gcd/div
-- support lemmas are not strict-purity clean, so this file keeps the public
-- bridge at the raw cross-multiplication surface.
private theorem qValid_qneg_pre (x : QRat) :
    qValid x -> qValid (qneg x) := by
  cases x with
  | mk num den =>
      intro hx
      unfold qValid at hx ⊢
      exact hx

theorem qToBRat_qrawAdd (x y : QRat) (hx : qValid x) (hy : qValid y) :
    RatEq (qToBRat (qrawAdd x y))
      (ratAdd (qToBRat x) (qToBRat y)) := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          unfold qValid at hx hy
          unfold qrawAdd
          rw [qToBRat_valid_eq_raw
            (x := qraw (xn * Int.ofNat yd + yn * Int.ofNat xd) (xd * yd))
            (nat_mul_pos_local hx hy)]
          rw [qToBRat_valid_eq_raw (x := { num := xn, den := xd }) hx]
          rw [qToBRat_valid_eq_raw (x := { num := yn, den := yd }) hy]
          let rz := rawBRat (xn * Int.ofNat yd + yn * Int.ofNat xd)
            (xd * yd) (nat_mul_pos_local hx hy)
          let rx := rawBRat xn xd hx
          let ry := rawBRat yn yd hy
          change RatEq rz (ratAdd rx ry)
          apply ratEq_of_num_den_intEq
          · change IntEq
              (intToBEDC (xn * Int.ofNat yd + yn * Int.ofNat xd))
              (IntAdd
                (IntMul (intToBEDC xn) (intToBEDC (Int.ofNat yd)))
                (IntMul (intToBEDC yn) (intToBEDC (Int.ofNat xd))))
            exact IntEq_trans (intToBEDC_add (xn * Int.ofNat yd) (yn * Int.ofNat xd))
              (BEDC.Derived.RationalUp.IntAdd_respects
                (intToBEDC_mul xn (Int.ofNat yd))
                (intToBEDC_mul yn (Int.ofNat xd)))
          · have leftDen :
                IntEq (ratDenInt rz) (intToBEDC (Int.ofNat (xd * yd))) := by
              unfold rz
              exact denInt_raw _ _ _
            have rightDenStructured :
                IntEq (ratDenInt (ratAdd rx ry))
                  (IntMul (ratDenInt rx) (ratDenInt ry)) :=
              ratDenInt_add rx ry
            have rightDen :
                IntEq (ratDenInt (ratAdd rx ry))
                (intToBEDC (Int.ofNat (xd * yd))) := by
              have rxDen : IntEq (ratDenInt rx) (intToBEDC (Int.ofNat xd)) := by
                unfold rx
                exact denInt_raw _ _ _
              have ryDen : IntEq (ratDenInt ry) (intToBEDC (Int.ofNat yd)) := by
                unfold ry
                exact denInt_raw _ _ _
              exact IntEq_trans rightDenStructured
                (IntEq_trans
                  (BEDC.Derived.RationalUp.IntMul_respects rxDen ryDen)
                (IntEq_symm (intToBEDC_nat_mul xd yd)))
            exact IntEq_trans leftDen (IntEq_symm rightDen)

theorem qToBRat_qrawSub (x y : QRat) (hx : qValid x) (hy : qValid y) :
    RatEq (qToBRat (qrawSub x y))
      (ratSub (qToBRat x) (qToBRat y)) := by
  unfold qrawSub ratSub
  exact RatEq_trans _ _ _
    (qToBRat_qrawAdd x (qneg y) hx (qValid_qneg_pre y hy))
    (ratAdd_respects (RatEq_refl (qToBRat x)) (qToBRat_qneg y))

theorem qToBRat_qrawMul (x y : QRat) (hx : qValid x) (hy : qValid y) :
    RatEq (qToBRat (qrawMul x y))
      (ratMul (qToBRat x) (qToBRat y)) := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          unfold qValid at hx hy
          unfold qrawMul
          rw [qToBRat_valid_eq_raw
            (x := qraw (xn * yn) (xd * yd)) (nat_mul_pos_local hx hy)]
          rw [qToBRat_valid_eq_raw (x := { num := xn, den := xd }) hx]
          rw [qToBRat_valid_eq_raw (x := { num := yn, den := yd }) hy]
          let rz := rawBRat (xn * yn) (xd * yd) (nat_mul_pos_local hx hy)
          let rx := rawBRat xn xd hx
          let ry := rawBRat yn yd hy
          change RatEq rz (ratMul rx ry)
          apply ratEq_of_num_den_intEq
          · change IntEq (intToBEDC (xn * yn))
              (IntMul (intToBEDC xn) (intToBEDC yn))
            exact intToBEDC_mul xn yn
          · have leftDen :
                IntEq (ratDenInt rz) (intToBEDC (Int.ofNat (xd * yd))) := by
              unfold rz
              exact denInt_raw _ _ _
            have rightDenStructured :
                IntEq (ratDenInt (ratMul rx ry))
                  (IntMul (ratDenInt rx) (ratDenInt ry)) :=
              ratDenInt_mul rx ry
            have rightDen :
                IntEq (ratDenInt (ratMul rx ry))
                  (intToBEDC (Int.ofNat (xd * yd))) := by
              have rxDen : IntEq (ratDenInt rx) (intToBEDC (Int.ofNat xd)) := by
                unfold rx
                exact denInt_raw _ _ _
              have ryDen : IntEq (ratDenInt ry) (intToBEDC (Int.ofNat yd)) := by
                unfold ry
                exact denInt_raw _ _ _
              exact IntEq_trans rightDenStructured
                (IntEq_trans
                  (BEDC.Derived.RationalUp.IntMul_respects rxDen ryDen)
                  (IntEq_symm (intToBEDC_nat_mul xd yd)))
            exact IntEq_trans leftDen (IntEq_symm rightDen)

theorem qToBRat_qrawDivNat (x : QRat) (n : Nat) (hx : qValid x) (hn : 0 < n) :
    RatEq (qToBRat (qrawDivNat x n))
      (ratMul (qToBRat x) (ratInvNat n)) := by
  cases x with
  | mk xn xd =>
      unfold qValid at hx
      unfold qrawDivNat
      rw [qToBRat_valid_eq_raw (x := qraw xn (xd * n))
        (nat_mul_pos_local hx hn)]
      rw [qToBRat_valid_eq_raw (x := { num := xn, den := xd }) hx]
      unfold ratInvNat
      rw [qToBRat_valid_eq_raw (x := qraw 1 n) hn]
      let rz := rawBRat xn (xd * n) (nat_mul_pos_local hx hn)
      let rx := rawBRat xn xd hx
      let rn := rawBRat 1 n hn
      change RatEq rz (ratMul rx rn)
      apply ratEq_of_num_den_intEq
      · change IntEq (intToBEDC xn) (IntMul (intToBEDC xn) (intToBEDC 1))
        exact IntEq_symm (intMul_one_right (intToBEDC xn))
      · have leftDen :
            IntEq (ratDenInt rz) (intToBEDC (Int.ofNat (xd * n))) := by
          unfold rz
          exact denInt_raw _ _ _
        have rightDenStructured :
            IntEq (ratDenInt (ratMul rx rn))
              (IntMul (ratDenInt rx) (ratDenInt rn)) :=
          ratDenInt_mul rx rn
        have rightDen :
            IntEq (ratDenInt (ratMul rx rn))
              (intToBEDC (Int.ofNat (xd * n))) := by
          have rxDen : IntEq (ratDenInt rx) (intToBEDC (Int.ofNat xd)) := by
            unfold rx
            exact denInt_raw _ _ _
          have rnDen : IntEq (ratDenInt rn) (intToBEDC (Int.ofNat n)) := by
            unfold rn
            exact denInt_raw _ _ _
          exact IntEq_trans rightDenStructured
            (IntEq_trans
              (BEDC.Derived.RationalUp.IntMul_respects rxDen rnDen)
              (IntEq_symm (intToBEDC_nat_mul xd n)))
        exact IntEq_trans leftDen (IntEq_symm rightDen)

private theorem qValid_qrawMul (x y : QRat) (hx : qValid x) (hy : qValid y) :
    qValid (qrawMul x y) := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          unfold qValid at hx hy
          change 0 < xd * yd
          exact nat_mul_pos_local hx hy

private theorem qValid_qrawAdd (x y : QRat) (hx : qValid x) (hy : qValid y) :
    qValid (qrawAdd x y) := by
  cases x with
  | mk xn xd =>
      cases y with
      | mk yn yd =>
          unfold qValid at hx hy
          change 0 < xd * yd
          exact nat_mul_pos_local hx hy

private theorem qValid_qrawDivNat (x : QRat) (n : Nat) (hx : qValid x) (hn : 0 < n) :
    qValid (qrawDivNat x n) := by
  cases x with
  | mk xn xd =>
      unfold qValid at hx
      change 0 < xd * n
      exact nat_mul_pos_local hx hn

theorem evalRaw_valid (p : Poly) (x : QRat) :
    qValid x -> polyValid p -> qValid (evalRaw p x) := by
  induction p with
  | nil =>
      intro _ _
      unfold evalRaw qzero qraw qValid
      exact Nat.succ_pos 0
  | cons a rest ih =>
      intro hx hp
      unfold evalRaw
      exact qValid_qrawAdd a (qrawMul x (evalRaw rest x))
        hp.left
        (qValid_qrawMul x (evalRaw rest x) hx (ih hx hp.right))

theorem antiderivRawFrom_valid (n : Nat) (p : Poly) :
    0 < n -> polyValid p -> polyValid (antiderivRawFrom n p) := by
  induction p generalizing n with
  | nil =>
      intro _ _
      unfold antiderivRawFrom polyValid
      trivial
  | cons a rest ih =>
      intro hn hp
      unfold antiderivRawFrom polyValid
      exact ⟨qValid_qrawDivNat a n hp.left hn,
        ih (n + 1) (Nat.succ_pos n) hp.right⟩

theorem antiderivRaw_valid (p : Poly) :
    polyValid p -> polyValid (antiderivRaw p) := by
  intro hp
  unfold antiderivRaw polyValid
  exact ⟨by unfold qValid qzero qraw; exact Nat.succ_pos 0,
    antiderivRawFrom_valid 1 p (Nat.succ_pos 0) hp⟩

theorem evalRaw_readback (p : Poly) (x : QRat) (hx : qValid x) (hp : polyValid p) :
    RatEq (qToBRat (evalRaw p x)) (evalB p (qToBRat x)) := by
  induction p with
  | nil =>
      unfold evalRaw evalB
      exact qToBRat_qzero
  | cons a rest ih =>
      unfold evalRaw evalB
      have hrest : qValid (evalRaw rest x) := evalRaw_valid rest x hx hp.right
      exact RatEq_trans _ _ _
        (qToBRat_qrawAdd a (qrawMul x (evalRaw rest x)) hp.left
          (qValid_qrawMul x (evalRaw rest x) hx hrest))
        (ratAdd_respects (RatEq_refl (qToBRat a))
          (RatEq_trans _ _ _
            (qToBRat_qrawMul x (evalRaw rest x) hx hrest)
            (ratMul_respects (RatEq_refl (qToBRat x)) (ih hp.right))))

theorem antiderivRaw_coeff_readback (n : Nat) (p : Poly)
    (hn : 0 < n) (hp : polyValid p) :
    List.length (antiderivRawFrom n p) = List.length (antiderivBFrom n p) := by
  induction p generalizing n with
  | nil => rfl
  | cons a rest ih =>
      unfold antiderivRawFrom antiderivBFrom
      exact congrArg Nat.succ (ih (n + 1) (Nat.succ_pos n) hp.right)

theorem evalBRats_antiderivB_cons (a : QRat) (rest : Poly) (n : Nat) (x : BRat) :
    evalBRats (antiderivBFrom n (a :: rest)) x =
      ratAdd (ratMul (qToBRat a) (ratInvNat n))
        (ratMul x (evalBRats (antiderivBFrom (n + 1) rest) x)) := by
  rfl

theorem antiderivRawFrom_eval_readback (n : Nat) (p : Poly) (y : QRat)
    (hn : 0 < n) (hp : polyValid p) (hy : qValid y) :
    RatEq
      (qToBRat (evalRaw (antiderivRawFrom n p) y))
      (evalBRats (antiderivBFrom n p) (qToBRat y)) := by
  induction p generalizing n with
  | nil =>
      unfold antiderivRawFrom evalRaw antiderivBFrom evalBRats
      exact qToBRat_qzero
  | cons a rest ih =>
      unfold antiderivRawFrom antiderivBFrom evalRaw evalBRats
      have hcoeff : qValid (qrawDivNat a n) :=
        qValid_qrawDivNat a n hp.left hn
      have htailValid : polyValid (antiderivRawFrom (n + 1) rest) :=
        antiderivRawFrom_valid (n + 1) rest (Nat.succ_pos n) hp.right
      have htailEval : qValid (evalRaw (antiderivRawFrom (n + 1) rest) y) :=
        evalRaw_valid (antiderivRawFrom (n + 1) rest) y hy htailValid
      exact RatEq_trans _ _ _
        (qToBRat_qrawAdd (qrawDivNat a n)
          (qrawMul y (evalRaw (antiderivRawFrom (n + 1) rest) y))
          hcoeff
          (qValid_qrawMul y (evalRaw (antiderivRawFrom (n + 1) rest) y)
            hy htailEval))
        (ratAdd_respects
          (qToBRat_qrawDivNat a n hp.left hn)
          (RatEq_trans _ _ _
            (qToBRat_qrawMul y
              (evalRaw (antiderivRawFrom (n + 1) rest) y) hy htailEval)
            (ratMul_respects (RatEq_refl (qToBRat y))
              (ih (n + 1) (Nat.succ_pos n) hp.right))))

theorem antiderivRaw_eval_readback (p : Poly) (y : QRat)
    (hp : polyValid p) (hy : qValid y) :
    RatEq
      (qToBRat (evalRaw (antiderivRaw p) y))
      (evalBRats (antiderivB p) (qToBRat y)) := by
  unfold antiderivRaw antiderivB evalRaw evalBRats
  have htailValid : polyValid (antiderivRawFrom 1 p) :=
    antiderivRawFrom_valid 1 p (Nat.succ_pos 0) hp
  have htailEval : qValid (evalRaw (antiderivRawFrom 1 p) y) :=
    evalRaw_valid (antiderivRawFrom 1 p) y hy htailValid
  exact RatEq_trans _ _ _
    (qToBRat_qrawAdd qzero (qrawMul y (evalRaw (antiderivRawFrom 1 p) y))
      (by unfold qValid qzero qraw; exact Nat.succ_pos 0)
      (qValid_qrawMul y (evalRaw (antiderivRawFrom 1 p) y) hy htailEval))
    (ratAdd_respects qToBRat_qzero
      (RatEq_trans _ _ _
        (qToBRat_qrawMul y (evalRaw (antiderivRawFrom 1 p) y) hy htailEval)
        (ratMul_respects (RatEq_refl (qToBRat y))
          (antiderivRawFrom_eval_readback 1 p y (Nat.succ_pos 0) hp hy))))

theorem evalB_cons (a : QRat) (p : Poly) (x : BRat) :
    evalB (a :: p) x = ratAdd (qToBRat a) (ratMul x (evalB p x)) := by
  rfl

theorem evalBRats_cons (a : BRat) (p : List BRat) (x : BRat) :
    evalBRats (a :: p) x = ratAdd a (ratMul x (evalBRats p x)) := by
  rfl

end BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly
