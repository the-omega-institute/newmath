import BEDC.Derived.PadicUp.FieldCore

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp

def ZpAgreeUpto {p : BHist} (N : Nat) (x y : ZpInt p) : Prop :=
  ∀ M : Nat, M ≤ N ->
    (zpLevel x (zpuNatToUnary M) (zpuNatToUnary_unary M)).val =
      (zpLevel y (zpuNatToUnary M) (zpuNatToUnary_unary M)).val

structure ZpCauchyData {p : BHist} (xs : Nat -> ZpInt p) where
  mu : Nat -> Nat
  cauchy : ∀ N i j : Nat, mu N ≤ i -> mu N ≤ j -> ZpAgreeUpto N (xs i) (xs j)

def zpCauchyEnvelope {p : BHist} {xs : Nat -> ZpInt p}
    (c : ZpCauchyData xs) : Nat -> Nat
  | 0 => c.mu 0
  | n + 1 => zpCauchyEnvelope c n + c.mu (n + 1)

theorem zpCauchyEnvelope_ge_mu {p : BHist} {xs : Nat -> ZpInt p}
    (c : ZpCauchyData xs) :
    ∀ N : Nat, c.mu N ≤ zpCauchyEnvelope c N := by
  intro N
  induction N with
  | zero =>
      exact Nat.le_refl _
  | succ N _ih =>
      unfold zpCauchyEnvelope
      exact Nat.le_add_left _ _

theorem zpCauchyEnvelope_monotone_step {p : BHist} {xs : Nat -> ZpInt p}
    (c : ZpCauchyData xs) (N : Nat) :
    zpCauchyEnvelope c N ≤ zpCauchyEnvelope c (N + 1) := by
  cases N with
  | zero =>
      unfold zpCauchyEnvelope
      exact Nat.le_add_right _ _
  | succ N =>
      unfold zpCauchyEnvelope
      exact Nat.le_add_right _ _

theorem zpCauchyEnvelope_ge_mu_of_le {p : BHist} {xs : Nat -> ZpInt p}
    (c : ZpCauchyData xs) {M N : Nat} (leMN : M ≤ N) :
    c.mu M ≤ zpCauchyEnvelope c N := by
  induction N generalizing M with
  | zero =>
      have mZero : M = 0 := Nat.eq_zero_of_le_zero leMN
      cases mZero
      exact zpCauchyEnvelope_ge_mu c 0
  | succ N ih =>
      cases Nat.eq_or_lt_of_le leMN with
      | inl same =>
          cases same
          exact zpCauchyEnvelope_ge_mu c (N + 1)
      | inr strict =>
          exact Nat.le_trans (ih (Nat.le_of_lt_succ strict))
            (zpCauchyEnvelope_monotone_step c N)

theorem zpNatToUnary_append_hsame_of_le :
    ∀ {M N : Nat}, M ≤ N ->
      ∃ K : BHist, UnaryHistory K ∧
        hsame (zpuNatToUnary N) (BEDC.FKernel.Cont.append (zpuNatToUnary M) K)
  | 0, N, _leMN =>
      ⟨zpuNatToUnary N, zpuNatToUnary_unary N,
        (append_empty_left (zpuNatToUnary N)).symm⟩
  | M + 1, 0, leMN =>
      False.elim (Nat.not_succ_le_zero M leMN)
  | M + 1, N + 1, leMN => by
      have tailLe : M ≤ N := Nat.succ_le_succ_iff.mp leMN
      cases zpNatToUnary_append_hsame_of_le tailLe with
      | intro K data =>
          exact
            ⟨K, data.left,
              (congrArg BHist.e1 data.right).trans
                (unary_append_e1_left (h := K) (k := zpuNatToUnary M) data.left).symm⟩

theorem zp_trunc_drop_nat_index {p : BHist} (x : ZpInt p) {M N : Nat}
    (leMN : M ≤ N) :
    hsame
      (natModFn (pPowCanon p (zpuNatToUnary M))
        (zpLevel x (zpuNatToUnary N) (zpuNatToUnary_unary N)).val)
      (zpLevel x (zpuNatToUnary M) (zpuNatToUnary_unary M)).val := by
  cases zpNatToUnary_append_hsame_of_le leMN with
  | intro K data =>
      have appendUnary : UnaryHistory (BEDC.FKernel.Cont.append (zpuNatToUnary M) K) :=
        unary_append_closed (zpuNatToUnary_unary M) data.left
      have drop := zp_trunc_drop_nat x (zpuNatToUnary_unary M) data.left
      have levelTransport :
          hsame
            (zpLevel x (zpuNatToUnary N) (zpuNatToUnary_unary N)).val
            (zpLevel x (BEDC.FKernel.Cont.append (zpuNatToUnary M) K)
              appendUnary).val :=
        zpTrunc_level_hsame x (zpuNatToUnary_unary N) appendUnary data.right
      exact hsame_trans
        (natModFn_hsame_arg_transport (M := pPowCanon p (zpuNatToUnary M))
          levelTransport)
        drop

theorem zp_trunc_same_of_agree_upto {p : BHist} {x y : ZpInt p}
    {M N : Nat} (agree : ZpAgreeUpto N x y) (leMN : M ≤ N) :
    hsame
      (natModFn (pPowCanon p (zpuNatToUnary M))
        (zpLevel y (zpuNatToUnary N) (zpuNatToUnary_unary N)).val)
      (zpLevel x (zpuNatToUnary M) (zpuNatToUnary_unary M)).val := by
  have drop := zp_trunc_drop_nat_index y leMN
  have sameLevel := agree M leMN
  exact hsame_trans drop (hsame_symm sameLevel)

def zpLimitTrunc {p : BHist} (xs : Nat -> ZpInt p)
    (c : ZpCauchyData xs) (N : BHist) (_NUnary : UnaryHistory N) : ZpTrunc p N :=
  (xs (zpCauchyEnvelope c (bwordLength N))).trunc N _NUnary

theorem zpLimitTrunc_compat {p : BHist} (xs : Nat -> ZpInt p)
    (c : ZpCauchyData xs) :
    ZpCompatible p (xs (c.mu 0)).prime (fun N NUnary => zpLimitTrunc xs c N NUnary) := by
  intro N NUnary
  unfold zpLimitTrunc
  change hsame
    (natModFn (pPowCanon p N)
      ((xs (zpCauchyEnvelope c (bwordLength (BHist.e1 N)))).trunc
        (BHist.e1 N) (unary_e1_closed NUnary)).val)
    ((xs (zpCauchyEnvelope c (bwordLength N))).trunc N NUnary).val
  have stepIndex :
      bwordLength (BHist.e1 N) = bwordLength N + 1 := rfl
  rw [stepIndex]
  have nextDrop :=
    (xs (zpCauchyEnvelope c (bwordLength N + 1))).compat N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod at nextDrop
  have agree :
      ZpAgreeUpto (bwordLength N)
        (xs (zpCauchyEnvelope c (bwordLength N + 1)))
        (xs (zpCauchyEnvelope c (bwordLength N))) := by
    exact c.cauchy (bwordLength N)
      (zpCauchyEnvelope c (bwordLength N + 1))
      (zpCauchyEnvelope c (bwordLength N))
      (Nat.le_trans (zpCauchyEnvelope_ge_mu c (bwordLength N))
        (zpCauchyEnvelope_monotone_step c (bwordLength N)))
      (zpCauchyEnvelope_ge_mu c (bwordLength N))
  have sameLevel := agree (bwordLength N) (Nat.le_refl _)
  have sameN :
      hsame
        ((xs (zpCauchyEnvelope c (bwordLength N + 1))).trunc N NUnary).val
        ((xs (zpCauchyEnvelope c (bwordLength N))).trunc N NUnary).val := by
    change hsame
      (zpLevel (xs (zpCauchyEnvelope c (bwordLength N + 1))) N NUnary).val
      (zpLevel (xs (zpCauchyEnvelope c (bwordLength N))) N NUnary).val
    have standardSame : hsame (zpuNatToUnary (bwordLength N)) N :=
      zpu_natToUnary_hsame_of_length NUnary
    have leftTransport :
        hsame
          (zpLevel (xs (zpCauchyEnvelope c (bwordLength N + 1))) N NUnary).val
          (zpLevel (xs (zpCauchyEnvelope c (bwordLength N + 1)))
            (zpuNatToUnary (bwordLength N))
            (zpuNatToUnary_unary (bwordLength N))).val :=
      zpTrunc_level_hsame
        (xs (zpCauchyEnvelope c (bwordLength N + 1)))
        NUnary (zpuNatToUnary_unary (bwordLength N)) (hsame_symm standardSame)
    have rightTransport :
        hsame
          (zpLevel (xs (zpCauchyEnvelope c (bwordLength N)))
            (zpuNatToUnary (bwordLength N))
            (zpuNatToUnary_unary (bwordLength N))).val
          (zpLevel (xs (zpCauchyEnvelope c (bwordLength N))) N NUnary).val :=
      zpTrunc_level_hsame
        (xs (zpCauchyEnvelope c (bwordLength N)))
        (zpuNatToUnary_unary (bwordLength N)) NUnary standardSame
    exact hsame_trans leftTransport (hsame_trans sameLevel rightTransport)
  exact hsame_trans nextDrop sameN

def zpLimit {p : BHist} (xs : Nat -> ZpInt p) (c : ZpCauchyData xs) : ZpInt p :=
  { prime := (xs (c.mu 0)).prime
    trunc := fun N NUnary => zpLimitTrunc xs c N NUnary
    compat := zpLimitTrunc_compat xs c }

theorem zpLimit_level_nat {p : BHist} (xs : Nat -> ZpInt p)
    (c : ZpCauchyData xs) (N : Nat) :
    (zpLevel (zpLimit xs c) (zpuNatToUnary N) (zpuNatToUnary_unary N)).val =
      (zpLevel (xs (zpCauchyEnvelope c N)) (zpuNatToUnary N)
        (zpuNatToUnary_unary N)).val := by
  unfold zpLevel zpLimit zpLimitTrunc
  change
    ((xs (zpCauchyEnvelope c (bwordLength (zpuNatToUnary N)))).trunc
      (zpuNatToUnary N) (zpuNatToUnary_unary N)).val =
      ((xs (zpCauchyEnvelope c N)).trunc
        (zpuNatToUnary N) (zpuNatToUnary_unary N)).val
  rw [zpuNatToUnary_length]

theorem zpLimit_converges {p : BHist} (xs : Nat -> ZpInt p)
    (c : ZpCauchyData xs) :
    ∀ N i : Nat, c.mu N ≤ i -> ZpAgreeUpto N (xs i) (zpLimit xs c) := by
  intro N i tail M leMN
  have envTail : c.mu N ≤ zpCauchyEnvelope c N :=
    zpCauchyEnvelope_ge_mu c N
  have agree : ZpAgreeUpto N (xs i) (xs (zpCauchyEnvelope c N)) :=
    c.cauchy N i (zpCauchyEnvelope c N) tail envTail
  have limitLevel :
      (zpLevel (zpLimit xs c) (zpuNatToUnary M)
        (zpuNatToUnary_unary M)).val =
        (zpLevel (xs (zpCauchyEnvelope c M)) (zpuNatToUnary M)
          (zpuNatToUnary_unary M)).val :=
    zpLimit_level_nat xs c M
  have envAgree : ZpAgreeUpto M (xs (zpCauchyEnvelope c N))
      (xs (zpCauchyEnvelope c M)) :=
    c.cauchy M (zpCauchyEnvelope c N) (zpCauchyEnvelope c M)
      (zpCauchyEnvelope_ge_mu_of_le c leMN)
      (zpCauchyEnvelope_ge_mu c M)
  exact (agree M leMN).trans ((envAgree M (Nat.le_refl _)).trans limitLevel.symm)

structure ZpCompleteSummary (p : BHist) where
  limit : {xs : Nat -> ZpInt p} -> ZpCauchyData xs -> ZpInt p
  converges : ∀ {xs : Nat -> ZpInt p} (c : ZpCauchyData xs),
    ∀ N i : Nat, c.mu N ≤ i -> ZpAgreeUpto N (xs i) (limit c)

def ZpInt_complete (p : BHist) : ZpCompleteSummary p :=
  { limit := fun c => zpLimit _ c
    converges := fun c => zpLimit_converges _ c }

theorem ZpAgreeUpto_right_eq {p : BHist} {N : Nat} {x y z : ZpInt p} :
    ZpAgreeUpto N x y -> ZpEq y z -> ZpAgreeUpto N x z := by
  intro agree same M leMN
  exact (agree M leMN).trans (same (zpuNatToUnary M) (zpuNatToUnary_unary M))

def qpClearDenomAt {p : BHist} (prime : NatPrime p) (K : Nat)
    (x : QpInt p) : ZpInt p :=
  zpScale p prime (K - x.shift) x.value

def QpAgreeUptoAt {p : BHist} (prime : NatPrime p) (K N : Nat)
    (x y : QpInt p) : Prop :=
  ZpAgreeUpto N (qpClearDenomAt prime K x) (qpClearDenomAt prime K y)

structure QpAgreeUptoCert {p : BHist} (N : Nat) (x y : QpInt p) where
  prime : NatPrime p
  commonShift : Nat
  leftBound : x.shift ≤ commonShift
  rightBound : y.shift ≤ commonShift
  agree : QpAgreeUptoAt prime commonShift N x y

def QpAgreeUpto {p : BHist} (N : Nat) (x y : QpInt p) : Prop :=
  Nonempty (QpAgreeUptoCert N x y)

structure QpCauchyData {p : BHist} (xs : Nat -> QpInt p) where
  mu : Nat -> Nat
  denomBound : Nat
  bounded : ∀ i : Nat, (xs i).shift ≤ denomBound
  cauchy : ∀ N i j : Nat, mu N ≤ i -> mu N ≤ j ->
    QpAgreeUptoAt (xs 0).value.prime denomBound N (xs i) (xs j)

def qpCauchyAgree {p : BHist} {xs : Nat -> QpInt p}
    (c : QpCauchyData xs) {N i j : Nat}
    (hi : c.mu N ≤ i) (hj : c.mu N ≤ j) : QpAgreeUpto N (xs i) (xs j) :=
  ⟨{ prime := (xs 0).value.prime
     commonShift := c.denomBound
     leftBound := c.bounded i
     rightBound := c.bounded j
     agree := c.cauchy N i j hi hj }⟩

def qpShiftedSeq {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) : Nat -> ZpInt p :=
  fun i => qpClearDenomAt (xs 0).value.prime c.denomBound (xs i)

def qpShiftedCauchyData {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) : ZpCauchyData (qpShiftedSeq xs c) :=
  { mu := c.mu
    cauchy := fun N i j hi hj => c.cauchy N i j hi hj }

def qpLimit {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) : QpInt p :=
  { shift := c.denomBound
    value := zpLimit (qpShiftedSeq xs c) (qpShiftedCauchyData xs c) }

theorem qpLimit_clear_bound {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) :
    ZpEq (zpLimit (qpShiftedSeq xs c) (qpShiftedCauchyData xs c))
      (qpClearDenomAt (xs 0).value.prime c.denomBound (qpLimit xs c)) := by
  unfold qpClearDenomAt qpLimit
  dsimp
  rw [Nat.sub_self]
  exact ZpEq_symm
    (zpOne_mul_left p (xs 0).value.prime
      (zpLimit (qpShiftedSeq xs c) (qpShiftedCauchyData xs c)))

theorem qpLimit_converges_at_bound {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) :
    ∀ N i : Nat, c.mu N ≤ i ->
      QpAgreeUptoAt (xs 0).value.prime c.denomBound N (xs i) (qpLimit xs c) := by
  intro N i tail
  exact ZpAgreeUpto_right_eq
    (zpLimit_converges (qpShiftedSeq xs c) (qpShiftedCauchyData xs c) N i tail)
    (qpLimit_clear_bound xs c)

theorem qpLimit_converges {p : BHist} (xs : Nat -> QpInt p)
    (c : QpCauchyData xs) :
    ∀ N i : Nat, c.mu N ≤ i -> QpAgreeUpto N (xs i) (qpLimit xs c) := by
  intro N i tail
  exact
    ⟨{ prime := (xs 0).value.prime
       commonShift := c.denomBound
       leftBound := c.bounded i
       rightBound := Nat.le_refl c.denomBound
       agree := qpLimit_converges_at_bound xs c N i tail }⟩

structure QpCompleteSummary (p : BHist) where
  zIntegerCompleteness : ZpCompleteSummary p
  limit : {xs : Nat -> QpInt p} -> QpCauchyData xs -> QpInt p
  converges : ∀ {xs : Nat -> QpInt p} (c : QpCauchyData xs),
    ∀ N i : Nat, c.mu N ≤ i -> QpAgreeUpto N (xs i) (limit c)

def Qp_complete (p : BHist) : QpCompleteSummary p :=
  { zIntegerCompleteness := ZpInt_complete p
    limit := fun c => qpLimit _ c
    converges := fun c => qpLimit_converges _ c }

end BEDC.Derived.PadicUp
