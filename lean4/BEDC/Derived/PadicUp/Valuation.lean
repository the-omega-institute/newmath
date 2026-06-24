import BEDC.Derived.PadicUp.ExactDivision
import BEDC.Derived.PadicUp.IntegerTower.Completeness
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.Order
import BEDC.Derived.IntUp.OneSidedContext

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

theorem qpVal_target_classifier {p : BHist} {x : QpInt p}
    {j k : BHist × BHist} :
    QpVal x j -> IntPairClassifier j k -> QpVal x k := by
  intro val target
  cases val with
  | intro y data =>
      cases data with
      | intro w rest =>
          exact ⟨y, w, rest.left,
            IntPairClassifier_equivalence_fields.right.right.right.right.left
              rest.right target⟩

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

theorem nat_succ_add_tail_eq (a t : Nat) : a + (t + 1) = a + 1 + t := by
  calc
    a + (t + 1) = a + (1 + t) := by
      rw [Nat.add_comm t 1]
    _ = a + 1 + t := by
      exact (Nat.add_assoc a 1 t).symm

def natLtTail : Nat -> Nat -> Nat
  | 0, 0 => 0
  | 0, b + 1 => b
  | _a + 1, 0 => 0
  | a + 1, b + 1 => natLtTail a b

theorem nat_lt_as_succ_add {a b : Nat} :
    a < b -> b = a + 1 + natLtTail a b := by
  induction a generalizing b with
  | zero =>
      intro hlt
      cases b with
      | zero =>
          cases hlt
      | succ b =>
          change Nat.succ b = 0 + 1 + b
          rw [Nat.zero_add]
          exact Nat.add_comm b 1
  | succ a ih =>
      intro hlt
      cases b with
      | zero =>
          cases hlt
      | succ b =>
          have tailLt : a < b := Nat.succ_lt_succ_iff.mp hlt
          have ihEq := ih tailLt
          let t := natLtTail a b
          change Nat.succ b = (a + 1) + 1 + t
          calc
            Nat.succ b = Nat.succ (a + 1 + t) := congrArg Nat.succ ihEq
            _ = (a + 1 + t) + 1 := rfl
            _ = (a + 1) + (t + 1) := by
              exact Nat.add_assoc (a + 1) t 1
            _ = (a + 1) + 1 + t := nat_succ_add_tail_eq (a + 1) t

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

theorem zpLevel_zero_lower_of_index_le {p : BHist} (a : ZpInt p)
    {lo hi : Nat} :
    (∃ tail : Nat, hi = lo + tail) ->
      (zpLevel a (zpuNatToUnary hi) (zpuNatToUnary_unary hi)).val =
        BHist.Empty ->
        (zpLevel a (zpuNatToUnary lo) (zpuNatToUnary_unary lo)).val =
          BHist.Empty := by
  intro leData zeroHi
  cases leData with
  | intro tail hiEq =>
      let L := zpuNatToUnary lo
      let T := zpuNatToUnary tail
      let H := zpuNatToUnary hi
      have LUnary : UnaryHistory L := zpuNatToUnary_unary lo
      have TUnary : UnaryHistory T := zpuNatToUnary_unary tail
      have HUnary : UnaryHistory H := zpuNatToUnary_unary hi
      have appendSame : hsame (BEDC.FKernel.Cont.append L T) H := by
        have addSame := zpuNatToUnary_add_hsame lo tail
        have sumSame : hsame (zpuNatToUnary (lo + tail)) H := by
          subst hi
          exact hsame_refl _
        exact hsame_trans addSame sumSame
      have zeroAtAppend :
          hsame
            (a.trunc (BEDC.FKernel.Cont.append L T)
              (unary_append_closed LUnary TUnary)).val
            BHist.Empty :=
        hsame_trans
          (zpTrunc_level_hsame a
            (unary_append_closed LUnary TUnary) HUnary appendSame)
          zeroHi
      have drop :=
        zp_trunc_drop_nat a LUnary TUnary
      have modZero :
          hsame
            (natModFn (pPowCanon p L)
              (a.trunc (BEDC.FKernel.Cont.append L T)
                (unary_append_closed LUnary TUnary)).val)
            BHist.Empty :=
        hsame_trans
          (natModFn_hsame_arg_transport (M := pPowCanon p L) zeroAtAppend)
          (hsame_refl BHist.Empty)
      exact hsame_trans (hsame_symm drop) modZero

def ZpValWitness_transport {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpValWitness y -> ZpValWitness x := by
  intro same w
  refine
    { k := w.k
      zero_k := ?_
      nz_succ := ?_ }
  · exact ZpEq_level_empty_transport (zpuNatToUnary_unary w.k) same w.zero_k
  · intro xZero
    exact w.nz_succ
      (ZpEq_level_empty_transport (zpuNatToUnary_unary (w.k + 1))
        (ZpEq_symm same) xZero)

def ZpValWitness_add_exact_of_lt {p : BHist} {x y : ZpInt p}
    (wx : ZpValWitness x) (wy : ZpValWitness y) :
    wx.k < wy.k -> ZpValWitness (zpAdd p x y) := by
  intro hlt
  let tail := natLtTail wx.k wy.k
  have wyEq : wy.k = wx.k + 1 + tail := by
    exact nat_lt_as_succ_add hlt
  have yZeroK :
      (zpLevel y (zpuNatToUnary wx.k) (zpuNatToUnary_unary wx.k)).val =
        BHist.Empty := by
    apply zpLevel_zero_lower_of_index_le y
    · exact ⟨tail + 1, Eq.trans wyEq (nat_succ_add_tail_eq wx.k tail).symm⟩
    · exact wy.zero_k
  have yZeroSucc :
      (zpLevel y (zpuNatToUnary (wx.k + 1))
        (zpuNatToUnary_unary (wx.k + 1))).val =
        BHist.Empty := by
    apply zpLevel_zero_lower_of_index_le y
    · exact ⟨tail, wyEq⟩
    · exact wy.zero_k
  refine
    { k := wx.k
      zero_k := ?_
      nz_succ := ?_ }
  · exact zpAdd_level_empty_of_both x y
      (zpuNatToUnary_unary wx.k) wx.zero_k yZeroK
  · intro sumZero
    have addToX :
        hsame ((zpAdd p x y).trunc (zpuNatToUnary (wx.k + 1))
          (zpuNatToUnary_unary (wx.k + 1))).val
          (x.trunc (zpuNatToUnary (wx.k + 1))
            (zpuNatToUnary_unary (wx.k + 1))).val :=
      zpAdd_level_zero_right x y
        (zpuNatToUnary_unary (wx.k + 1)) yZeroSucc
    exact wx.nz_succ (hsame_trans (hsame_symm addToX) sumZero)

def ZpValWitness_add_exact_of_gt {p : BHist} {x y : ZpInt p}
    (wx : ZpValWitness x) (wy : ZpValWitness y) :
    wy.k < wx.k -> ZpValWitness (zpAdd p x y) := by
  intro hgt
  exact ZpValWitness_transport (zpAdd_comm p x y)
    (ZpValWitness_add_exact_of_lt wy wx hgt)

def valuation_add_exact_of_lt {p : BHist} {a b : ZpInt p}
    (wa : ZpValWitness a) (wb : ZpValWitness b) :
    wa.k < wb.k -> ZpValWitness (zpAdd p a b) :=
  ZpValWitness_add_exact_of_lt wa wb

def valuation_add_exact_of_gt {p : BHist} {a b : ZpInt p}
    (wa : ZpValWitness a) (wb : ZpValWitness b) :
    wb.k < wa.k -> ZpValWitness (zpAdd p a b) :=
  ZpValWitness_add_exact_of_gt wa wb

theorem natOne_not_empty : hsame NatOne BHist.Empty -> False := by
  intro same
  exact not_hsame_e1_empty same

def ZpValWitness_one {p : BHist} (prime : NatPrime p) :
    ZpValWitness (zpOne p prime) := by
  refine
    { k := 0
      zero_k := zpLevel_zero_val_empty (zpOne p prime)
      nz_succ := ?_ }
  intro oneZero
  unfold zpLevel zpOne natToZp fromNatModPow natMod at oneZero
  change hsame (natModFn (pPowCanon p (zpuNatToUnary 1)) NatOne)
    BHist.Empty at oneZero
  have onePowerSame : hsame (pPowCanon p (zpuNatToUnary 1)) p := by
    change hsame (pPowCanon p (BHist.e1 BHist.Empty)) p
    exact pPowCanon_one_hsame prime
  have modAtPrime :
      hsame (natModFn p NatOne) BHist.Empty :=
    hsame_trans (hsame_symm (natModFn_hsame_mod_transport onePowerSame))
      oneZero
  have oneMod :
      hsame (natModFn p NatOne) NatOne :=
    natModFn_of_strict prime.left (NatPrime_empty_absurd prime)
      (unary_e1_closed unary_empty) prime.right.left
  exact natOne_not_empty (hsame_trans (hsame_symm oneMod) modAtPrime)

def ZpValWitness_pUnit {p : BHist} (prime : NatPrime p) :
    ZpValWitness (pUnitZp p prime) := by
  refine
    { k := 1
      zero_k := ?_
      nz_succ := ?_ }
  · unfold zpLevel pUnitZp natToZp fromNatModPow natMod
    change hsame (natModFn (pPowCanon p (zpuNatToUnary 1)) p)
      BHist.Empty
    have onePowerSame : hsame (pPowCanon p (zpuNatToUnary 1)) p := by
      change hsame (pPowCanon p (BHist.e1 BHist.Empty)) p
      exact pPowCanon_one_hsame prime
    have pDivides : NatDivides p p :=
      (NatDivides_reflexive_pair prime.left).right
    have modZero :
        hsame (natModFn p p) BHist.Empty :=
      (dvd_iff_mod_zero prime.left (NatPrime_empty_absurd prime) prime.left).mp
        pDivides
    exact hsame_trans (natModFn_hsame_mod_transport onePowerSame) modZero
  · intro pUnitZeroAtTwo
    have factor :
        ZpEq (pUnitZp p prime)
          (zpMul p (zpPowP p prime 1) (zpOne p prime)) := by
      have left :
          ZpEq (pUnitZp p prime)
            (zpMul p (zpOne p prime) (pUnitZp p prime)) :=
        ZpEq_symm (zpOne_mul_left p prime (pUnitZp p prime))
      have right :
          ZpEq (zpMul p (zpOne p prime) (pUnitZp p prime))
            (zpMul p (zpPowP p prime 1) (zpOne p prime)) := by
        unfold zpPowP pPowZp
        exact ZpEq_symm
          (zpOne_mul_right p prime
            (zpMul p (zpOne p prime) (pUnitZp p prime)))
      exact ZpEq_trans left right
    have productZeroAtTwo :
        (zpLevel (zpMul p (zpPowP p prime 1) (zpOne p prime))
          (zpuNatToUnary (1 + 1)) (zpuNatToUnary_unary (1 + 1))).val =
          BHist.Empty :=
      ZpEq_level_empty_transport (zpuNatToUnary_unary (1 + 1))
        (ZpEq_symm factor) pUnitZeroAtTwo
    have oneZeroAtOne :
        (zpLevel (zpOne p prime) (zpuNatToUnary 1)
          (zpuNatToUnary_unary 1)).val = BHist.Empty :=
      powP_mul_level_succ_zero_cancel prime 1 (zpOne p prime)
        productZeroAtTwo
    exact (ZpValWitness_one prime).nz_succ oneZeroAtOne

def ZpValWitness_powP {p : BHist} (prime : NatPrime p) :
    (k : Nat) -> ZpValWitness (zpPowP p prime k)
  | 0 => ZpValWitness_one prime
  | k + 1 =>
      ZpValWitness_mul (ZpValWitness_powP prime k) (ZpValWitness_pUnit prime)

theorem ZpValWitness_powP_k {p : BHist} (prime : NatPrime p) (k : Nat) :
    (ZpValWitness_powP prime k).k = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      unfold ZpValWitness_powP
      unfold ZpValWitness_mul
      dsimp
      rw [ih]
      unfold ZpValWitness_pUnit
      rfl

def ZpValWitness_scale {p : BHist} {x : ZpInt p}
    (prime : NatPrime p) (n : Nat) (wx : ZpValWitness x) :
    ZpValWitness (zpScale p prime n x) :=
  ZpValWitness_mul (ZpValWitness_powP prime n) wx

theorem ZpValWitness_scale_k {p : BHist} {x : ZpInt p}
    (prime : NatPrime p) (n : Nat) (wx : ZpValWitness x) :
    (ZpValWitness_scale prime n wx).k = n + wx.k := by
  unfold ZpValWitness_scale ZpValWitness_mul
  dsimp
  rw [ZpValWitness_powP_k prime n]

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

theorem qpRawValPair_scale_left_classified {p : BHist}
    (prime : NatPrime p) (x : QpInt p) (wx : ZpValWitness x.value)
    (n : Nat) :
    IntPairClassifier
      (qpRawValPair { shift := x.shift + n, value := zpScale p prime n x.value }
        (ZpValWitness_scale prime n wx))
      (qpRawValPair x wx) := by
  let scaled : QpInt p :=
    { shift := x.shift + n, value := zpScale p prime n x.value }
  have rawCarrier := qpRawValPair_carrier scaled (ZpValWitness_scale prime n wx)
  have targetCarrier := qpRawValPair_carrier x wx
  have posSame :
      hsame
        (qpRawValPair scaled (ZpValWitness_scale prime n wx)).1
        (BEDC.FKernel.Cont.append (zpuNatToUnary n)
          (qpRawValPair x wx).1) := by
    unfold qpRawValPair QpValIndex scaled
    dsimp
    change hsame (zpuNatToUnary (ZpValWitness_scale prime n wx).k)
      (BEDC.FKernel.Cont.append (zpuNatToUnary n) (zpuNatToUnary wx.k))
    have kEq := ZpValWitness_scale_k prime n wx
    rw [kEq]
    exact hsame_symm (zpuNatToUnary_add_hsame n wx.k)
  have negSame :
      hsame
        (qpRawValPair scaled (ZpValWitness_scale prime n wx)).2
        (BEDC.FKernel.Cont.append (qpRawValPair x wx).2
          (zpuNatToUnary n)) := by
    unfold qpRawValPair QpValIndex scaled
    dsimp
    exact hsame_symm (zpuNatToUnary_add_hsame x.shift n)
  have contextual :
      IntPairClassifier
        (BEDC.FKernel.Cont.append (zpuNatToUnary n) (qpRawValPair x wx).1,
          BEDC.FKernel.Cont.append (qpRawValPair x wx).2 (zpuNatToUnary n))
        (BEDC.FKernel.Cont.append (zpuNatToUnary n) (qpRawValPair x wx).1,
          BEDC.FKernel.Cont.append (qpRawValPair x wx).2 (zpuNatToUnary n)) :=
    IntPairClassifier_equivalence_fields.right.right.left
      ⟨unary_append_closed (zpuNatToUnary_unary n) targetCarrier.left,
        unary_append_closed targetCarrier.right (zpuNatToUnary_unary n)⟩
  have scaledToContext :
      IntPairClassifier (qpRawValPair scaled (ZpValWitness_scale prime n wx))
        (BEDC.FKernel.Cont.append (zpuNatToUnary n) (qpRawValPair x wx).1,
          BEDC.FKernel.Cont.append (qpRawValPair x wx).2 (zpuNatToUnary n)) :=
    IntPairClassifier_equivalence_fields.right.right.right.right.right
      (qpRawValPair_refl scaled (ZpValWitness_scale prime n wx))
      (hsame_refl _) (hsame_refl _) posSame negSame rawCarrier
      ⟨unary_append_closed (zpuNatToUnary_unary n) targetCarrier.left,
        unary_append_closed targetCarrier.right (zpuNatToUnary_unary n)⟩
  have contextToTarget :
      IntPairClassifier
        (BEDC.FKernel.Cont.append (zpuNatToUnary n) (qpRawValPair x wx).1,
          BEDC.FKernel.Cont.append (qpRawValPair x wx).2 (zpuNatToUnary n))
        (qpRawValPair x wx) :=
    by
      constructor
      · exact ⟨unary_append_closed (zpuNatToUnary_unary n) targetCarrier.left,
          unary_append_closed targetCarrier.right (zpuNatToUnary_unary n)⟩
      · constructor
        · exact targetCarrier
        · have leftAssoc :
            hsame
              (BEDC.FKernel.Cont.append
                (BEDC.FKernel.Cont.append (zpuNatToUnary n) (qpRawValPair x wx).1)
                (qpRawValPair x wx).2)
              (BEDC.FKernel.Cont.append (zpuNatToUnary n)
                (BEDC.FKernel.Cont.append (qpRawValPair x wx).1
                  (qpRawValPair x wx).2)) :=
            append_assoc (zpuNatToUnary n) (qpRawValPair x wx).1
              (qpRawValPair x wx).2
          have commute :
            hsame
              (BEDC.FKernel.Cont.append (zpuNatToUnary n)
                (BEDC.FKernel.Cont.append (qpRawValPair x wx).1
                  (qpRawValPair x wx).2))
              (BEDC.FKernel.Cont.append
                (BEDC.FKernel.Cont.append (qpRawValPair x wx).1
                  (qpRawValPair x wx).2)
                (zpuNatToUnary n)) :=
            unary_append_comm (zpuNatToUnary_unary n)
              (unary_append_closed targetCarrier.left targetCarrier.right)
          have rightAssoc :
            hsame
              (BEDC.FKernel.Cont.append
                (BEDC.FKernel.Cont.append (qpRawValPair x wx).1
                  (qpRawValPair x wx).2)
                (zpuNatToUnary n))
              (BEDC.FKernel.Cont.append (qpRawValPair x wx).1
                (BEDC.FKernel.Cont.append (qpRawValPair x wx).2
                  (zpuNatToUnary n))) :=
            append_assoc (qpRawValPair x wx).1 (qpRawValPair x wx).2
              (zpuNatToUnary n)
          exact hsame_trans leftAssoc (hsame_trans commute rightAssoc)
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    scaledToContext contextToTarget

theorem qpVal_add_eq_left_of_lt {p : BHist} (x y : QpInt p)
    (hx : QpApart0 x) (hy : QpApart0 y) :
    intLt (qpVal x hx) (qpVal y hy) ->
      QpVal (qpAdd x y) (qpVal x hx) := by
  intro hlt
  let wx := firstNonzero hx.num_apart
  let wy := firstNonzero hy.num_apart
  let sx := ZpValWitness_scale x.value.prime y.shift wx
  let sy := ZpValWitness_scale x.value.prime x.shift wy
  have sxK : sx.k = y.shift + wx.k := ZpValWitness_scale_k x.value.prime y.shift wx
  have syK : sy.k = x.shift + wy.k := ZpValWitness_scale_k x.value.prime x.shift wy
  have indexLt : sx.k < sy.k := by
    unfold intLt qpVal qpRawValPair QpValIndex at hlt
    dsimp at hlt
    rw [zpuNatToUnary_length] at hlt
    rw [zpuNatToUnary_length] at hlt
    rw [zpuNatToUnary_length] at hlt
    rw [zpuNatToUnary_length] at hlt
    rw [sxK, syK]
    rw [Nat.add_comm y.shift wx.k]
    rw [Nat.add_comm x.shift wy.k]
    exact hlt
  let sumW := ZpValWitness_add_exact_of_lt sx sy indexLt
  have valueEq :
      ZpEq (qpAdd x y).value
        (zpAdd p (zpScale p x.value.prime y.shift x.value)
          (zpScale p x.value.prime x.shift y.value)) :=
    qpAdd_value_canonical x.value.prime x y
  let raw : QpInt p :=
    { shift := x.shift + y.shift
      value := zpAdd p (zpScale p x.value.prime y.shift x.value)
        (zpScale p x.value.prime x.shift y.value) }
  have sameRaw : QpEq (qpAdd x y) raw := by
    apply QpEq_of_shift_value
    · rfl
    · exact valueEq
  have rawVal : QpVal raw (qpRawValPair raw sumW) :=
    qpVal_of_witness raw sumW
  let scaledX : QpInt p :=
    { shift := x.shift + y.shift
      value := zpScale p x.value.prime y.shift x.value }
  have sumToScaledX :
      IntPairClassifier (qpRawValPair raw sumW)
        (qpRawValPair scaledX sx) := by
    have rawCarrier := qpRawValPair_carrier raw sumW
    have targetCarrier := qpRawValPair_carrier scaledX sx
    have posSame :
        hsame (qpRawValPair raw sumW).1
          (qpRawValPair scaledX sx).1 := by
      unfold qpRawValPair QpValIndex raw sumW ZpValWitness_add_exact_of_lt
      dsimp
      rfl
    have negSame :
        hsame (qpRawValPair raw sumW).2
          (qpRawValPair scaledX sx).2 := by
      unfold qpRawValPair QpValIndex raw scaledX
      dsimp
      exact hsame_refl _
    exact IntPairClassifier_equivalence_fields.right.right.right.right.right
      (qpRawValPair_refl raw sumW)
      (hsame_refl _) (hsame_refl _) posSame negSame rawCarrier targetCarrier
  have scaledXToX :
      IntPairClassifier
        (qpRawValPair scaledX sx)
        (qpRawValPair x wx) := by
    exact qpRawValPair_scale_left_classified x.value.prime x wx y.shift
  have rawToX :
      IntPairClassifier (qpRawValPair raw sumW) (qpRawValPair x wx) :=
    IntPairClassifier_equivalence_fields.right.right.right.right.left
      sumToScaledX scaledXToX
  exact qpVal_target_classifier (qpVal_well_defined (QpEq_symm sameRaw) rawVal)
    rawToX

theorem qpVal_add_eq_right_of_lt {p : BHist} (x y : QpInt p)
    (hx : QpApart0 x) (hy : QpApart0 y) :
    intLt (qpVal y hy) (qpVal x hx) ->
      QpVal (qpAdd x y) (qpVal y hy) := by
  intro hlt
  have comm : QpEq (qpAdd x y) (qpAdd y x) := qpAdd_comm x y
  exact qpVal_well_defined (QpEq_symm comm)
    (qpVal_add_eq_left_of_lt y x hy hx hlt)

theorem qpVal_add_eq_min_of_ne {p : BHist} (x y : QpInt p)
    (hx : QpApart0 x) (hy : QpApart0 y) :
    (IntPairClassifier (qpVal x hx) (qpVal y hy) -> False) ->
      QpVal (qpAdd x y) (intMin (qpVal x hx) (qpVal y hy)) := by
  intro notSame
  let vx := qpVal x hx
  let vy := qpVal y hy
  have vxCarrier : IntPairCarrier vx.1 vx.2 := by
    unfold vx qpVal qpRawValPair QpValIndex
    exact ⟨zpuNatToUnary_unary (firstNonzero hx.num_apart).k,
      zpuNatToUnary_unary x.shift⟩
  have vyCarrier : IntPairCarrier vy.1 vy.2 := by
    unfold vy qpVal qpRawValPair QpValIndex
    exact ⟨zpuNatToUnary_unary (firstNonzero hy.num_apart).k,
      zpuNatToUnary_unary y.shift⟩
  by_cases hle :
      BEDC.FKernel.ExternalBinary.bwordLength vx.1 +
          BEDC.FKernel.ExternalBinary.bwordLength vy.2 ≤
        BEDC.FKernel.ExternalBinary.bwordLength vy.1 +
          BEDC.FKernel.ExternalBinary.bwordLength vx.2
  · have notEq :
        ¬ BEDC.FKernel.ExternalBinary.bwordLength vx.1 +
            BEDC.FKernel.ExternalBinary.bwordLength vy.2 =
          BEDC.FKernel.ExternalBinary.bwordLength vy.1 +
            BEDC.FKernel.ExternalBinary.bwordLength vx.2 := by
      intro lenEq
      have sourceUnary : UnaryHistory (BEDC.FKernel.Cont.append vx.1 vy.2) :=
        unary_append_closed vxCarrier.left vyCarrier.right
      have targetUnary : UnaryHistory (BEDC.FKernel.Cont.append vy.1 vx.2) :=
        unary_append_closed vyCarrier.left vxCarrier.right
      have same : hsame (BEDC.FKernel.Cont.append vx.1 vy.2)
          (BEDC.FKernel.Cont.append vy.1 vx.2) :=
        (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
          sourceUnary targetUnary).mpr (by
            rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
            rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
            exact lenEq)
      exact notSame ⟨vxCarrier, vyCarrier, same⟩
    have hlt : intLt vx vy := by
      unfold intLt
      exact Nat.lt_of_le_of_ne hle notEq
    have valLeft : QpVal (qpAdd x y) vx :=
      qpVal_add_eq_left_of_lt x y hx hy hlt
    exact qpVal_target_classifier valLeft
      (IntPairClassifier_equivalence_fields.right.right.right.left
        (intMin_left_classifier_of_lt vxCarrier vyCarrier hlt))
  · have hgt : intLt vy vx := by
      unfold intLt
      exact Nat.lt_of_not_ge hle
    have valRight : QpVal (qpAdd x y) vy :=
      qpVal_add_eq_right_of_lt x y hx hy hgt
    exact qpVal_target_classifier valRight
      (IntPairClassifier_equivalence_fields.right.right.right.left
        (intMin_right_classifier_of_lt vxCarrier vyCarrier hgt))

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
  strong_add_cert : ∀ (x y : QpInt p) (hx : QpApart0 x) (hy : QpApart0 y),
    (IntPairClassifier (val x hx) (val y hy) -> False) ->
      val_rel (qpAdd x y) (intMin (val x hx) (val y hy))

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
    add_min_cert := qpVal_add_min
    strong_add_cert := qpVal_add_eq_min_of_ne }

structure QpValuedFieldSummary (p : BHist) where
  field_core : QpFieldCore p
  valuation_core : QpValuationCore p
  completeness : QpCompleteSummary p

def QpInt_valued_field (p : BHist) : QpValuedFieldSummary p :=
  { field_core := QpInt_field_core p
    valuation_core := QpInt_valuation_core p
    completeness := Qp_complete p }

end BEDC.Derived.PadicUp
