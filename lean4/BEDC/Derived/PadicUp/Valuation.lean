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

theorem ZpUnit_mul {p : BHist} {x y : ZpInt p} :
    ZpUnit x -> ZpUnit y -> ZpUnit (zpMul p x y) := by
  intro xUnit yUnit
  unfold ZpUnit at xUnit yUnit
  unfold ZpUnit
  intro productZero
  let One := BHist.e1 BHist.Empty
  have OneUnary : UnaryHistory One := unary_e1_closed unary_empty
  let M := pPowCanon p One
  let xr := (zpLevel x One OneUnary).val
  let yr := (zpLevel y One OneUnary).val
  have onePowerSame : hsame M p := pPowCanon_one_hsame x.prime
  let xBounded : BoundedNat p :=
    { val := xr
      isLt :=
        NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure
          (zpLevel x One OneUnary).isLt onePowerSame }
  let yBounded : BoundedNat p :=
    { val := yr
      isLt :=
        NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure
          (zpLevel y One OneUnary).isLt onePowerSame }
  have productZeroAtP :
      hsame (natModFn p (natMulFn xBounded.val yBounded.val)) BHist.Empty := by
    unfold zpLevel zpMul zpMulTrunc fromNatModPow natMod at productZero
    change hsame (natModFn M (natMulFn xBounded.val yBounded.val))
      BHist.Empty at productZero
    have modTransport :
        hsame (natModFn M (natMulFn xBounded.val yBounded.val))
          (natModFn p (natMulFn xBounded.val yBounded.val)) :=
      natModFn_hsame_mod_transport onePowerSame
    exact hsame_trans (hsame_symm modTransport) productZero
  exact prime_mod_mul_nonzero_bounded x.prime xBounded yBounded
    (by
      intro xZero
      exact xUnit xZero)
    (by
      intro yZero
      exact yUnit yZero)
    productZeroAtP

theorem powP_mul_level_succ_zero_cancel {p : BHist} (prime : NatPrime p)
    (k : Nat) (z : ZpInt p) :
    (zpLevel (zpMul p (zpPowP p prime k) z) (zpuNatToUnary (k + 1))
      (zpuNatToUnary_unary (k + 1))).val = BHist.Empty ->
      (zpLevel z (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
        BHist.Empty := by
  intro zeroScaled
  let N := zpuNatToUnary 1
  let K := zpuNatToUnary k
  let NK := BEDC.FKernel.Cont.append N K
  let S := zpuNatToUnary (k + 1)
  have NUnary : UnaryHistory N := zpuNatToUnary_unary 1
  have KUnary : UnaryHistory K := zpuNatToUnary_unary k
  have NKUnary : UnaryHistory NK := unary_append_closed NUnary KUnary
  have SUnary : UnaryHistory S := zpuNatToUnary_unary (k + 1)
  have sameNK : hsame NK S := zpuNatToUnary_succ_left_hsame k
  have zeroAtNK :
      hsame
        ((zpMul p (zpPowP p prime k) z).trunc NK NKUnary).val
        BHist.Empty := by
    have transport :
        hsame
          ((zpMul p (zpPowP p prime k) z).trunc NK NKUnary).val
          ((zpMul p (zpPowP p prime k) z).trunc S SUnary).val :=
      zpTrunc_level_hsame (zpMul p (zpPowP p prime k) z)
        NKUnary SUnary sameNK
    exact hsame_trans transport zeroScaled
  unfold zpPowP at zeroAtNK
  have powerToNat := pPowZp_natToZp p prime k
  have zeroAtNK' :
      hsame
        (natModFn (pPowCanon p NK)
          (natMulFn
            (natModFn (pPowCanon p NK) (pPowCanon p K))
            (z.trunc NK NKUnary).val))
        BHist.Empty := by
    change hsame
      (natModFn (pPowCanon p NK)
        (natMulFn ((zpPowP p prime k).trunc NK NKUnary).val
          (z.trunc NK NKUnary).val))
      (natModFn (pPowCanon p NK) BHist.Empty) at zeroAtNK
    have lhsTransport :
        hsame
          (natModFn (pPowCanon p NK)
            (natMulFn ((zpPowP p prime k).trunc NK NKUnary).val
              (z.trunc NK NKUnary).val))
          (natModFn (pPowCanon p NK)
            (natMulFn
              (natModFn (pPowCanon p NK) (pPowCanon p K))
              (z.trunc NK NKUnary).val)) := by
      exact natModFn_hsame_arg_transport (M := pPowCanon p NK)
        (natMulFn_hsame_transport (powerToNat NK NKUnary) (hsame_refl _))
    exact hsame_trans (hsame_symm lhsTransport) zeroAtNK
  have MUnary : UnaryHistory (pPowCanon p NK) := pPowCanon_unary p NK
  have MNonempty : hsame (pPowCanon p NK) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NKUnary
  have productUnary :
      UnaryHistory (natMulFn (pPowCanon p K) (z.trunc NK NKUnary).val) :=
    natMulFn_unary (pPowCanon_unary p K)
      (BoundedNat_unary (pPowCanon_unary p NK) (z.trunc NK NKUnary))
  have dividesBigProduct :
      NatDivides (pPowCanon p NK)
        (natMulFn (pPowCanon p K) (z.trunc NK NKUnary).val) := by
    have reduceLeft :
        hsame
          (natModFn (pPowCanon p NK)
            (natMulFn (pPowCanon p K) (z.trunc NK NKUnary).val))
          (natModFn (pPowCanon p NK)
            (natMulFn
              (natModFn (pPowCanon p NK) (pPowCanon p K))
              (z.trunc NK NKUnary).val)) := by
      exact hsame_symm
        (natModFn_mul_left_reduce_same_mod MUnary MNonempty
          (pPowCanon_unary p K)
          (BoundedNat_unary (pPowCanon_unary p NK) (z.trunc NK NKUnary)))
    have modZero :
        hsame
          (natModFn (pPowCanon p NK)
            (natMulFn (pPowCanon p K) (z.trunc NK NKUnary).val))
          BHist.Empty :=
      hsame_trans reduceLeft zeroAtNK'
    exact (dvd_iff_mod_zero MUnary MNonempty productUnary).mpr modZero
  have pNDividesZAtNK : NatDivides (pPowCanon p N) (z.trunc NK NKUnary).val := by
    have powProduct : NatMul (pPowCanon p N) (pPowCanon p K) (pPowCanon p NK) := by
      have powN := pPowCanon_PPow prime.left NUnary
      have powK := pPowCanon_PPow prime.left KUnary
      have productTotal := NatMul_total (pPowCanon_unary p N) (pPowCanon_unary p K)
      cases productTotal with
      | intro product productData =>
          have add : NatAdd N K NK := ⟨NUnary, KUnary, rfl⟩
          have powProduct : PPow p NK product := PPow_add powN powK add productData.right
          have sameProduct : hsame product (pPowCanon p NK) :=
            PPow_functional powProduct (pPowCanon_PPow prime.left NKUnary)
          exact (NatMul_result_hsame_transport productData.right sameProduct).right
    have divisorSame :
        hsame (pPowCanon p NK) (natMulFn (pPowCanon p K) (pPowCanon p N)) :=
      NatMul_comm_hsame (pPowCanon_unary p N) (pPowCanon_unary p K)
        powProduct (natMulFn_rel (pPowCanon_unary p K) (pPowCanon_unary p N))
    have dividesTransported :
        NatDivides (natMulFn (pPowCanon p K) (pPowCanon p N))
          (natMulFn (pPowCanon p K) (z.trunc NK NKUnary).val) :=
      (NatDivides_divisor_hsame_transport dividesBigProduct divisorSame).right
    exact nat_dvd_cancel_left
      (pPowCanon_unary p K)
      (pPowCanon_nonempty_of_prime prime KUnary)
      (pPowCanon_unary p N)
      (BoundedNat_unary (pPowCanon_unary p NK) (z.trunc NK NKUnary))
      dividesTransported
  have zDrop := zp_trunc_drop_nat z NUnary KUnary
  have zNKModZero :
      hsame (natModFn (pPowCanon p N) (z.trunc NK NKUnary).val) BHist.Empty :=
    (dvd_iff_mod_zero (pPowCanon_unary p N)
      (pPowCanon_nonempty_of_prime prime NUnary)
      (BoundedNat_unary (pPowCanon_unary p NK) (z.trunc NK NKUnary))).mp
      pNDividesZAtNK
  change hsame (z.trunc N NUnary).val BHist.Empty
  exact hsame_trans (hsame_symm zDrop) zNKModZero

def ZpValWitness_mul {p : BHist} {x y : ZpInt p}
    (wx : ZpValWitness x) (wy : ZpValWitness y) :
    ZpValWitness (zpMul p x y) := by
  let sum := wx.k + wy.k
  let J := zpuNatToUnary wx.k
  let K := zpuNatToUnary wy.k
  let S := zpuNatToUnary sum
  refine
    { k := sum
      zero_k := ?_
      nz_succ := ?_ }
  · have JUnary : UnaryHistory J := zpuNatToUnary_unary wx.k
    have KUnary : UnaryHistory K := zpuNatToUnary_unary wy.k
    have JKUnary : UnaryHistory (BEDC.FKernel.Cont.append J K) :=
      unary_append_closed JUnary KUnary
    have SUnary : UnaryHistory S := zpuNatToUnary_unary sum
    have leftDivides :
        PDvdNat p J
          (x.trunc (BEDC.FKernel.Cont.append J K) JKUnary).val :=
      zpLevel_zero_ext_PDvdNat x JUnary KUnary wx.zero_k
    have rightRaw :
        PDvdNat p K
          (y.trunc (BEDC.FKernel.Cont.append K J)
            (unary_append_closed KUnary JUnary)).val :=
      zpLevel_zero_ext_PDvdNat y KUnary JUnary wy.zero_k
    have rightDivides :
        PDvdNat p K
          (y.trunc (BEDC.FKernel.Cont.append J K) JKUnary).val :=
      PDvdNat_hsame_exponent_result rightRaw (hsame_refl K)
        (zpTrunc_level_hsame y (unary_append_closed KUnary JUnary) JKUnary
          (unary_append_comm KUnary JUnary))
    have productZeroAtAppend :
        (zpLevel (zpMul p x y) (BEDC.FKernel.Cont.append J K) JKUnary).val =
          BHist.Empty :=
      zpMul_level_empty_of_PDvdNat_product x y JKUnary
        (NatAdd_append_self JUnary KUnary) leftDivides rightDivides
    have sameAppendS : hsame (BEDC.FKernel.Cont.append J K) S :=
      zpuNatToUnary_add_hsame wx.k wy.k
    change hsame
      ((zpMul p x y).trunc S SUnary).val BHist.Empty
    exact hsame_trans
      (zpTrunc_level_hsame (zpMul p x y) SUnary JKUnary
        (hsame_symm sameAppendS))
      productZeroAtAppend
  · intro productSuccZero
    let ux := zpDivPowExact x wx.k wx.zero_k
    let uy := zpDivPowExact y wy.k wy.zero_k
    let uxy := zpMul p ux uy
    have productUnit : ZpUnit uxy :=
      ZpUnit_mul (divPowExact_unit wx) (divPowExact_unit wy)
    have xFactor :
        ZpEq x (zpMul p (zpPowP p x.prime wx.k) ux) :=
      ZpEq_symm (pow_mul_divPowExact x wx.k wx.zero_k)
    have yFactor :
        ZpEq y (zpMul p (zpPowP p y.prime wy.k) uy) :=
      ZpEq_symm (pow_mul_divPowExact y wy.k wy.zero_k)
    have replaceXY :
        ZpEq (zpMul p x y)
          (zpMul p (zpMul p (zpPowP p x.prime wx.k) ux)
            (zpMul p (zpPowP p y.prime wy.k) uy)) :=
      zpMul_congr xFactor yFactor
    have shuffle :
        ZpEq
          (zpMul p (zpMul p (zpPowP p x.prime wx.k) ux)
            (zpMul p (zpPowP p y.prime wy.k) uy))
          (zpMul p
            (zpMul p (zpPowP p x.prime wx.k) (zpPowP p y.prime wy.k))
            uxy) :=
      zpMul_pair_shuffle p (zpPowP p x.prime wx.k) ux
        (zpPowP p y.prime wy.k) uy
    have switchRightPrime :
        ZpEq (zpPowP p y.prime wy.k) (zpPowP p x.prime wy.k) := by
      unfold zpPowP
      exact pPowZp_prime_irrel y.prime x.prime wy.k
    have powerAdd :
        ZpEq
          (zpMul p (zpPowP p x.prime wx.k) (zpPowP p y.prime wy.k))
          (zpPowP p x.prime sum) :=
      ZpEq_trans (zpMul_right_congr switchRightPrime)
        (pPowZp_mul_add p x.prime wx.k wy.k)
    have replacePower :
        ZpEq
          (zpMul p
            (zpMul p (zpPowP p x.prime wx.k) (zpPowP p y.prime wy.k))
            uxy)
          (zpMul p (zpPowP p x.prime sum) uxy) :=
      zpMul_left_congr powerAdd
    have productFactor :
        ZpEq (zpMul p x y) (zpMul p (zpPowP p x.prime sum) uxy) :=
      ZpEq_trans replaceXY (ZpEq_trans shuffle replacePower)
    have scaledSuccZero :
        (zpLevel (zpMul p (zpPowP p x.prime sum) uxy)
          (zpuNatToUnary (sum + 1)) (zpuNatToUnary_unary (sum + 1))).val =
          BHist.Empty :=
      ZpEq_level_empty_transport (zpuNatToUnary_unary (sum + 1))
        (ZpEq_symm productFactor) productSuccZero
    have unitZero :
        (zpLevel uxy (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
          BHist.Empty :=
      powP_mul_level_succ_zero_cancel x.prime sum uxy scaledSuccZero
    exact productUnit unitZero

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

theorem qpVal_mul_of_index_eq {p : BHist} (x y : QpInt p)
    (wx : ZpValWitness x.value) (wy : ZpValWitness y.value)
    (wxy : ZpValWitness (qpMul x y).value) :
    wxy.k = wx.k + wy.k ->
      QpVal (qpMul x y)
        (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy)) := by
  intro indexEq
  exact ⟨qpMul x y, wxy, QpEq_refl (qpMul x y),
    qpRawValPair_mul_classified_of_index_eq x y wx wy wxy indexEq⟩

def QpApart0_mul {p : BHist} {x y : QpInt p}
    (_hx : QpApart0 x) (_hy : QpApart0 y) : QpApart0 (qpMul x y) :=
  { num_apart := ZpApart0_of_witness
      (ZpValWitness_mul (firstNonzero _hx.num_apart)
        (firstNonzero _hy.num_apart)) }

theorem qpVal_mul {p : BHist} (x y : QpInt p)
    (hx : QpApart0 x) (hy : QpApart0 y) :
    QpVal (qpMul x y) (QpValAdd (qpVal x hx) (qpVal y hy)) := by
  let wx := firstNonzero hx.num_apart
  let wy := firstNonzero hy.num_apart
  let wxy := ZpValWitness_mul wx wy
  have indexEq :
      (firstNonzero (ZpApart0_of_witness wxy)).k = wx.k + wy.k := by
    exact Eq.trans (firstNonzero_of_witness_k wxy) rfl
  change QpVal (qpMul x y)
    (QpValAdd (qpRawValPair x wx) (qpRawValPair y wy))
  exact qpVal_mul_of_index_eq x y wx wy (firstNonzero (ZpApart0_of_witness wxy))
    indexEq

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
  mul_cert : ∀ (x y : QpInt p) (hx : QpApart0 x) (hy : QpApart0 y),
    val_rel (qpMul x y) (QpValAdd (val x hx) (val y hy))
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
