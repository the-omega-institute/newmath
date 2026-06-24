import BEDC.Derived.PadicUp.ExactDivision
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

-- ℚ_p 的值群用整数对编码: `(positive, negative)` 表示 positive - negative。
def qpRawValPair {p : BHist} (x : QpInt p) (w : ZpValWitness x.value) :
    BHist × BHist :=
  QpValIndex (zpuNatToUnary w.k) x.shift

def qpVal {p : BHist} (x : QpInt p) (hx : QpApart0 x) : BHist × BHist :=
  qpRawValPair x (firstNonzero hx.num_apart)

def QpValAdd (j k : BHist × BHist) : BHist × BHist :=
  pairAdd j k

def QpValNeg (j : BHist × BHist) : BHist × BHist :=
  pairNeg j

def QpValSub (j k : BHist × BHist) : BHist × BHist :=
  intSub j k

def QpNormIndex (j : BHist × BHist) : BHist × BHist :=
  QpValNeg j

theorem qpRawValPair_carrier {p : BHist} (x : QpInt p)
    (w : ZpValWitness x.value) :
    IntPairCarrier (qpRawValPair x w).1 (qpRawValPair x w).2 := by
  exact ⟨zpuNatToUnary_unary w.k, zpuNatToUnary_unary x.shift⟩

theorem qpRawValPair_refl {p : BHist} (x : QpInt p)
    (w : ZpValWitness x.value) :
    IntPairClassifier (qpRawValPair x w) (qpRawValPair x w) := by
  have carrier := qpRawValPair_carrier x w
  exact ⟨carrier, carrier, hsame_refl _⟩

def QpVal {p : BHist} (x : QpInt p) (j : BHist × BHist) : Prop :=
  ∃ y : QpInt p, ∃ w : ZpValWitness y.value,
    QpEq x y ∧ IntPairClassifier (qpRawValPair y w) j

theorem qpVal_of_witness {p : BHist} (x : QpInt p)
    (w : ZpValWitness x.value) :
    QpVal x (qpRawValPair x w) := by
  exact ⟨x, w, QpEq_refl x, qpRawValPair_refl x w⟩

theorem qpVal_of_apart {p : BHist} (x : QpInt p) (hx : QpApart0 x) :
    QpVal x (qpVal x hx) := by
  unfold qpVal
  exact qpVal_of_witness x (firstNonzero hx.num_apart)

theorem qpVal_well_defined {p : BHist} {x y : QpInt p} {j : BHist × BHist} :
    QpEq x y -> QpVal x j -> QpVal y j := by
  intro same val
  cases val with
  | intro r data =>
      cases data with
      | intro w rest =>
          exact ⟨r, w, QpEq_trans (QpEq_symm same) rest.left, rest.right⟩

theorem qpVal_well_defined_iff {p : BHist} {x y : QpInt p} {j : BHist × BHist} :
    QpEq x y -> (QpVal x j ↔ QpVal y j) := by
  intro same
  constructor
  · exact qpVal_well_defined same
  · exact qpVal_well_defined (QpEq_symm same)

def IntPairLe (a b : BHist × BHist) : Prop :=
  ∃ t : BHist, UnaryHistory t ∧
    IntPairClassifier (QpValAdd a (t, BHist.Empty)) b

theorem IntPairLe_refl (a : BHist × BHist)
    (carrier : IntPairCarrier a.1 a.2) :
    IntPairLe a a := by
  unfold IntPairLe QpValAdd
  have zeroCarrier : IntPairCarrier BHist.Empty BHist.Empty :=
    ⟨unary_empty, unary_empty⟩
  have addCarrier : IntPairCarrier (pairAdd a (BHist.Empty, BHist.Empty)).1
      (pairAdd a (BHist.Empty, BHist.Empty)).2 :=
    pairAdd_carrier carrier zeroCarrier
  have sameLeft :
      hsame (BEDC.FKernel.Cont.append
        (BEDC.FKernel.Cont.append a.1 BHist.Empty) a.2)
        (BEDC.FKernel.Cont.append a.1 a.2) := by
    exact congrArg (fun h => BEDC.FKernel.Cont.append h a.2)
      (append_empty_right a.1)
  have sameRight :
      hsame (BEDC.FKernel.Cont.append a.1 a.2)
        (BEDC.FKernel.Cont.append a.1
          (BEDC.FKernel.Cont.append a.2 BHist.Empty)) := by
    exact (congrArg (fun h => BEDC.FKernel.Cont.append a.1 h)
      (append_empty_right a.2)).symm
  exact ⟨BHist.Empty, unary_empty,
    ⟨addCarrier, carrier, hsame_trans sameLeft sameRight⟩⟩

def QpNorm {p : BHist} (x : QpInt p) (n : BHist × BHist) : Prop :=
  ∃ j : BHist × BHist, QpVal x j ∧ IntPairClassifier n (QpNormIndex j)

theorem qpNorm_of_val {p : BHist} {x : QpInt p} {j : BHist × BHist} :
    QpVal x j ->
      QpNorm x (QpNormIndex j) := by
  intro val
  have carrierJ : IntPairCarrier j.1 j.2 := by
    cases val with
    | intro y data =>
        cases data with
        | intro w rest =>
            exact rest.right.right.left
  have negCarrier : IntPairCarrier (QpNormIndex j).1 (QpNormIndex j).2 :=
    pairNeg_carrier carrierJ
  exact ⟨j, val, ⟨negCarrier, negCarrier, hsame_refl _⟩⟩

theorem qpNorm_well_defined {p : BHist} {x y : QpInt p} {n : BHist × BHist} :
    QpEq x y -> QpNorm x n -> QpNorm y n := by
  intro same norm
  cases norm with
  | intro j data =>
      exact ⟨j, qpVal_well_defined same data.left, data.right⟩

theorem nat_add_sub_cancel_left_pure (a b : Nat) : a + b - a = b := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.sub_zero b
  | succ a ih =>
      rw [Nat.succ_add]
      rw [Nat.succ_sub_succ]
      exact ih

def qpValClearDenomAt {p : BHist} (prime : NatPrime p) (K : Nat)
    (x : QpInt p) : ZpInt p :=
  zpScale p prime (K - x.shift) x.value

structure QpValLowerAt {p : BHist} (prime : NatPrime p) (K n : Nat)
    (x : QpInt p) where
  shift_le : x.shift ≤ K
  zero :
    (zpLevel (qpValClearDenomAt prime K x) (zpuNatToUnary n)
      (zpuNatToUnary_unary n)).val = BHist.Empty

def QpValLower {p : BHist} (x : QpInt p) (j : BHist × BHist) : Prop :=
  ∃ prime : NatPrime p, ∃ K : Nat, ∃ n : Nat,
    QpValLowerAt prime K n x ∧
      IntPairClassifier j (zpuNatToUnary n, zpuNatToUnary K)

theorem ZpEq_level_empty_transport {p N : BHist} {x y : ZpInt p}
    (NUnary : UnaryHistory N) :
    ZpEq x y ->
      (zpLevel y N NUnary).val = BHist.Empty ->
        (zpLevel x N NUnary).val = BHist.Empty := by
  intro same yZero
  exact hsame_trans (same N NUnary) yZero

theorem zpAdd_level_empty_of_both {p N : BHist} (x y : ZpInt p)
    (NUnary : UnaryHistory N) :
    (zpLevel x N NUnary).val = BHist.Empty ->
      (zpLevel y N NUnary).val = BHist.Empty ->
        (zpLevel (zpAdd p x y) N NUnary).val = BHist.Empty := by
  intro xZero yZero
  have addToX : hsame ((zpAdd p x y).trunc N NUnary).val (x.trunc N NUnary).val :=
    zpAdd_level_zero_right x y NUnary yZero
  exact hsame_trans addToX xZero

theorem qpValLower_of_apart {p : BHist} (x : QpInt p) (hx : QpApart0 x) :
    QpValLower x (qpVal x hx) := by
  let w := firstNonzero hx.num_apart
  have lowerAt : QpValLowerAt x.value.prime x.shift w.k x := by
    constructor
    · exact Nat.le_refl x.shift
    · unfold qpValClearDenomAt
      rw [Nat.sub_self]
      exact ZpEq_level_empty_transport (zpuNatToUnary_unary w.k)
        (zpOne_mul_left p x.value.prime x.value)
        w.zero_k
  exact ⟨x.value.prime, x.shift, w.k, lowerAt, qpRawValPair_refl x w⟩

theorem qpRawValPair_mul_classified_of_index_eq {p : BHist}
    (x y : QpInt p) (wx : ZpValWitness x.value)
    (wy : ZpValWitness y.value) (wxy : ZpValWitness (qpMul x y).value) :
    wxy.k = wx.k + wy.k ->
      IntPairClassifier (qpRawValPair (qpMul x y) wxy)
        (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)) := by
  intro indexEq
  have rawCarrier := qpRawValPair_carrier (qpMul x y) wxy
  have addCarrier : IntPairCarrier
      (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)).1
      (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)).2 :=
    pairAdd_carrier (qpRawValPair_carrier x wx) (qpRawValPair_carrier y wy)
  have posSame :
      hsame (qpRawValPair (qpMul x y) wxy).1
        (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)).1 := by
    unfold qpRawValPair QpValAdd pairAdd
    dsimp
    rw [indexEq]
    exact hsame_symm (zpuNatToUnary_add_hsame wx.k wy.k)
  have negSame :
      hsame (qpRawValPair (qpMul x y) wxy).2
        (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)).2 := by
    unfold qpRawValPair QpValAdd pairAdd qpMul
    dsimp
    exact hsame_symm (zpuNatToUnary_add_hsame x.shift y.shift)
  exact
    IntPairClassifier_equivalence_fields.right.right.right.right.right
      (qpRawValPair_refl (qpMul x y) wxy)
      (hsame_refl _) (hsame_refl _) posSame negSame rawCarrier addCarrier

theorem qpVal_mul {p : BHist} (x y : QpInt p)
    (wx : ZpValWitness x.value) (wy : ZpValWitness y.value)
    (wxy : ZpValWitness (qpMul x y).value) :
    wxy.k = wx.k + wy.k ->
      QpVal (qpMul x y)
        (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)) := by
  intro indexEq
  exact ⟨qpMul x y, wxy, QpEq_refl (qpMul x y),
    qpRawValPair_mul_classified_of_index_eq x y wx wy wxy indexEq⟩

def QpValCommonLower (lower left right : BHist × BHist) : Prop :=
  IntPairLe lower left ∧ IntPairLe lower right

theorem qpVal_add_min {p : BHist} (prime : NatPrime p)
    (x y : QpInt p) (n : Nat) :
    QpValLowerAt prime (x.shift + y.shift) n x ->
      QpValLowerAt prime (x.shift + y.shift) n y ->
        QpValLower (qpAdd x y)
          (zpuNatToUnary n, zpuNatToUnary (x.shift + y.shift)) := by
  intro lowerX lowerY
  let S := x.shift + y.shift
  let N := zpuNatToUnary n
  have NUnary : UnaryHistory N := zpuNatToUnary_unary n
  have xIndex : S - x.shift = y.shift := by
    unfold S
    exact nat_add_sub_cancel_left_pure x.shift y.shift
  have yIndex : S - y.shift = x.shift := by
    unfold S
    rw [Nat.add_comm x.shift y.shift]
    exact nat_add_sub_cancel_left_pure y.shift x.shift
  have xClear :
      ZpEq (qpValClearDenomAt prime S x) (zpScale p prime y.shift x.value) := by
    unfold qpValClearDenomAt S
    exact zpScale_nat_eq prime x.value xIndex
  have yClear :
      ZpEq (qpValClearDenomAt prime S y) (zpScale p prime x.shift y.value) := by
    unfold qpValClearDenomAt S
    exact zpScale_nat_eq prime y.value yIndex
  have xZero :
      (zpLevel (zpScale p prime y.shift x.value) N NUnary).val = BHist.Empty := by
    exact ZpEq_level_empty_transport NUnary (ZpEq_symm xClear) lowerX.zero
  have yZero :
      (zpLevel (zpScale p prime x.shift y.value) N NUnary).val = BHist.Empty := by
    exact ZpEq_level_empty_transport NUnary (ZpEq_symm yClear) lowerY.zero
  have sumZero :
      (zpLevel
        (zpAdd p (zpScale p prime y.shift x.value)
          (zpScale p prime x.shift y.value)) N NUnary).val = BHist.Empty :=
    zpAdd_level_empty_of_both
      (zpScale p prime y.shift x.value)
      (zpScale p prime x.shift y.value) NUnary xZero yZero
  have valueZero :
      (zpLevel (qpAdd x y).value N NUnary).val = BHist.Empty :=
    ZpEq_level_empty_transport NUnary (qpAdd_value_canonical prime x y) sumZero
  have clearZero :
      (zpLevel (qpValClearDenomAt prime S (qpAdd x y)) N NUnary).val =
        BHist.Empty := by
    have clearEq :
        ZpEq (qpValClearDenomAt prime S (qpAdd x y))
          (zpScale p prime 0 (qpAdd x y).value) := by
      unfold qpValClearDenomAt S
      exact zpScale_nat_eq prime (qpAdd x y).value (Nat.sub_self S)
    exact ZpEq_level_empty_transport NUnary
      (ZpEq_trans clearEq (zpOne_mul_left p prime (qpAdd x y).value))
      valueZero
  have lowerAt : QpValLowerAt prime S n (qpAdd x y) := by
    constructor
    · exact Nat.le_refl S
    · exact clearZero
  have pairCarrier : IntPairCarrier (zpuNatToUnary n) (zpuNatToUnary S) :=
    ⟨zpuNatToUnary_unary n, zpuNatToUnary_unary S⟩
  exact ⟨prime, S, n, lowerAt, ⟨pairCarrier, pairCarrier, hsame_refl _⟩⟩

structure QpValuationCore (p : BHist) where
  val : (x : QpInt p) -> QpApart0 x -> BHist × BHist
  val_rel : QpInt p -> BHist × BHist -> Prop
  val_of_apart : ∀ (x : QpInt p) (hx : QpApart0 x), val_rel x (val x hx)
  val_respects : ∀ {x y : QpInt p} {j : BHist × BHist},
    QpEq x y -> val_rel x j -> val_rel y j
  norm_rel : QpInt p -> BHist × BHist -> Prop
  norm_of_val : ∀ {x : QpInt p} {j : BHist × BHist},
    val_rel x j -> norm_rel x (QpNormIndex j)
  lower_rel : QpInt p -> BHist × BHist -> Prop
  lower_of_apart : ∀ (x : QpInt p) (hx : QpApart0 x), lower_rel x (val x hx)
  mul_cert : ∀ (x y : QpInt p)
    (wx : ZpValWitness x.value) (wy : ZpValWitness y.value)
    (wxy : ZpValWitness (qpMul x y).value),
      wxy.k = wx.k + wy.k ->
        val_rel (qpMul x y) (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy))
  add_min_cert : ∀ (prime : NatPrime p) (x y : QpInt p) (n : Nat),
    QpValLowerAt prime (x.shift + y.shift) n x ->
      QpValLowerAt prime (x.shift + y.shift) n y ->
        lower_rel (qpAdd x y)
          (zpuNatToUnary n, zpuNatToUnary (x.shift + y.shift))

def QpInt_valuation_core (p : BHist) : QpValuationCore p :=
  { val := qpVal
    val_rel := QpVal
    val_of_apart := qpVal_of_apart
    val_respects := qpVal_well_defined
    norm_rel := QpNorm
    norm_of_val := qpNorm_of_val
    lower_rel := QpValLower
    lower_of_apart := qpValLower_of_apart
    mul_cert := qpVal_mul
    add_min_cert := qpVal_add_min }

end BEDC.Derived.PadicUp
