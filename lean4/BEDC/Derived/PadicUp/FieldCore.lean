import BEDC.Derived.PadicUp.UnitInverse

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

theorem zpLevel_zero_ext_dvd {p : BHist} (a : ZpInt p)
    {K T : BHist} (KUnary : UnaryHistory K) (TUnary : UnaryHistory T)
    (zeroK : (zpLevel a K KUnary).val = BHist.Empty) :
    NatDivides (pPowCanon p K)
      (a.trunc (BEDC.FKernel.Cont.append K T)
        (unary_append_closed KUnary TUnary)).val := by
  have drop :=
    zp_trunc_drop_nat a KUnary TUnary
  have remZero :
      hsame
        (natModFn (pPowCanon p K)
          (a.trunc (BEDC.FKernel.Cont.append K T)
            (unary_append_closed KUnary TUnary)).val)
        BHist.Empty :=
    hsame_trans drop zeroK
  exact (dvd_iff_mod_zero
    (pPowCanon_unary p K)
    (pPowCanon_nonempty_of_prime a.prime KUnary)
    (BoundedNat_unary (pPowCanon_unary p (BEDC.FKernel.Cont.append K T))
      (a.trunc (BEDC.FKernel.Cont.append K T)
        (unary_append_closed KUnary TUnary)))).mpr remZero

theorem zpLevel_empty_of_dvd_level {p : BHist} (a : ZpInt p)
    {N : BHist} (NUnary : UnaryHistory N) :
    NatDivides (pPowCanon p N) (a.trunc N NUnary).val ->
      (zpLevel a N NUnary).val = BHist.Empty := by
  intro divides
  have remZero :
      hsame (natModFn (pPowCanon p N) (a.trunc N NUnary).val) BHist.Empty :=
    (dvd_iff_mod_zero
      (pPowCanon_unary p N)
      (pPowCanon_nonempty_of_prime a.prime NUnary)
      (BoundedNat_unary (pPowCanon_unary p N) (a.trunc N NUnary))).mp divides
  have remSelf :
      hsame (natModFn (pPowCanon p N) (a.trunc N NUnary).val)
        (a.trunc N NUnary).val :=
    natModFn_of_strict
      (pPowCanon_unary p N)
      (pPowCanon_nonempty_of_prime a.prime NUnary)
      (BoundedNat_unary (pPowCanon_unary p N) (a.trunc N NUnary))
      (a.trunc N NUnary).isLt
  exact hsame_trans (hsame_symm remSelf) remZero

theorem pPowCanon_one_hsame {p : BHist} (prime : NatPrime p) :
    hsame (pPowCanon p (BHist.e1 BHist.Empty)) p := by
  change hsame (zpuNatToUnary (bwordLength p ^ 1)) p
  exact zpu_hsame_of_unary_length (zpuNatToUnary_unary _) prime.left
    ((zpuNatToUnary_length _).trans (Nat.one_mul (bwordLength p)))

theorem zpuNatToUnary_add_hsame (m n : Nat) :
    hsame (BEDC.FKernel.Cont.append (zpuNatToUnary m) (zpuNatToUnary n))
      (zpuNatToUnary (m + n)) := by
  exact zpu_hsame_of_unary_length
    (unary_append_closed (zpuNatToUnary_unary m) (zpuNatToUnary_unary n))
    (zpuNatToUnary_unary (m + n))
    (by
      rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
      rw [zpuNatToUnary_length, zpuNatToUnary_length, zpuNatToUnary_length])

theorem zpuNatToUnary_succ_right_hsame (n : Nat) :
    hsame (BEDC.FKernel.Cont.append (zpuNatToUnary n) (zpuNatToUnary 1))
      (zpuNatToUnary (n + 1)) :=
  zpuNatToUnary_add_hsame n 1

theorem zpuNatToUnary_succ_left_hsame (n : Nat) :
    hsame (BEDC.FKernel.Cont.append (zpuNatToUnary 1) (zpuNatToUnary n))
      (zpuNatToUnary (n + 1)) := by
  exact hsame_trans (zpuNatToUnary_add_hsame 1 n)
    (zpu_hsame_of_unary_length
      (zpuNatToUnary_unary (1 + n))
      (zpuNatToUnary_unary (n + 1))
      (by rw [zpuNatToUnary_length, zpuNatToUnary_length, Nat.add_comm]))

theorem zpuNatToUnary_natAdd (m n : Nat) :
    NatAdd (zpuNatToUnary m) (zpuNatToUnary n) (zpuNatToUnary (m + n)) := by
  exact ⟨zpuNatToUnary_unary m, zpuNatToUnary_unary n,
    cont_intro (hsame_symm (zpuNatToUnary_add_hsame m n))⟩

theorem zpuNatToUnary_natAdd_succ_left (n : Nat) :
    NatAdd (zpuNatToUnary 1) (zpuNatToUnary n) (zpuNatToUnary (n + 1)) := by
  exact ⟨zpuNatToUnary_unary 1, zpuNatToUnary_unary n,
    cont_intro (hsame_symm (zpuNatToUnary_succ_left_hsame n))⟩

theorem zpTrunc_level_hsame {p N K : BHist} (x : ZpInt p)
    (NUnary : UnaryHistory N) (KUnary : UnaryHistory K) :
    hsame N K ->
      hsame (x.trunc N NUnary).val (x.trunc K KUnary).val := by
  intro same
  cases same
  rfl

theorem pPowCanon_hsame_level {p N K : BHist} :
    hsame N K -> hsame (pPowCanon p N) (pPowCanon p K) := by
  intro same
  cases same
  rfl

theorem PDvdNat_hsame_exponent_result {p k k' n n' : BHist} :
    PDvdNat p k n -> hsame k k' -> hsame n n' -> PDvdNat p k' n' := by
  intro divides sameK sameN
  cases PDvdNat_exponent_hsame_transport divides sameK with
  | intro pk data =>
      exact ⟨pk, data.left,
        (NatDivides_dividend_hsame_transport data.right sameN).right⟩

theorem zpLevel_empty_of_PDvdNat {p : BHist} (a : ZpInt p)
    {N : BHist} (NUnary : UnaryHistory N) :
    PDvdNat p N (a.trunc N NUnary).val ->
      (zpLevel a N NUnary).val = BHist.Empty := by
  intro divides
  cases divides with
  | intro pk data =>
      have samePower : hsame pk (pPowCanon p N) :=
        PPow_functional data.left (pPowCanon_PPow a.prime.left NUnary)
      exact zpLevel_empty_of_dvd_level a NUnary
        ((NatDivides_divisor_hsame_transport data.right samePower).right)

theorem zpLevel_zero_ext_PDvdNat {p : BHist} (a : ZpInt p)
    {K T : BHist} (KUnary : UnaryHistory K) (TUnary : UnaryHistory T)
    (zeroK : (zpLevel a K KUnary).val = BHist.Empty) :
    PDvdNat p K
      (a.trunc (BEDC.FKernel.Cont.append K T)
        (unary_append_closed KUnary TUnary)).val := by
  exact ⟨pPowCanon p K, pPowCanon_PPow a.prime.left KUnary,
    zpLevel_zero_ext_dvd a KUnary TUnary zeroK⟩

theorem PDvdNat_empty {p k : BHist} :
    UnaryHistory p -> UnaryHistory k -> PDvdNat p k BHist.Empty := by
  intro pUnary kUnary
  exact ⟨pPowCanon p k, pPowCanon_PPow pUnary kUnary,
    ⟨BHist.Empty, unary_empty, NatMul.zero (pPowCanon_unary p k)⟩⟩

theorem natModFn_empty_of_PDvdNat {p k n : BHist}
    (prime : NatPrime p) (kUnary : UnaryHistory k) (nUnary : UnaryHistory n) :
    PDvdNat p k n -> hsame (natModFn (pPowCanon p k) n) BHist.Empty := by
  intro divides
  cases divides with
  | intro pk data =>
      have samePower : hsame pk (pPowCanon p k) :=
        PPow_functional data.left (pPowCanon_PPow prime.left kUnary)
      have canonDivides :
          NatDivides (pPowCanon p k) n :=
        (NatDivides_divisor_hsame_transport data.right samePower).right
      exact (dvd_iff_mod_zero
        (pPowCanon_unary p k)
        (pPowCanon_nonempty_of_prime prime kUnary)
        nUnary).mp canonDivides

theorem PDvdNat_mod_self {p k n : BHist}
    (prime : NatPrime p) (kUnary : UnaryHistory k) (nUnary : UnaryHistory n) :
    PDvdNat p k n -> PDvdNat p k (natModFn (pPowCanon p k) n) := by
  intro divides
  have modZero := natModFn_empty_of_PDvdNat prime kUnary nUnary divides
  exact PDvdNat_hsame_exponent_result
    (PDvdNat_empty prime.left kUnary) (hsame_refl k) (hsame_symm modZero)

theorem zpMul_level_empty_of_PDvdNat_product {p N j k : BHist}
    (x y : ZpInt p) (NUnary : UnaryHistory N)
    (add : NatAdd j k N) :
    PDvdNat p j (x.trunc N NUnary).val ->
      PDvdNat p k (y.trunc N NUnary).val ->
        (zpLevel (zpMul p x y) N NUnary).val = BHist.Empty := by
  intro left right
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have productDivides :
      PDvdNat p N (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    PDvdNat_product_add left right add (natMulFn_rel xUnary yUnary)
  change (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)) = BHist.Empty
  exact natModFn_empty_of_PDvdNat x.prime NUnary (natMulFn_unary xUnary yUnary)
    productDivides

theorem error_pow_vanish {p : BHist} (e : ZpInt p)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) :
    ∀ n : Nat,
      (zpLevel (zpPow p e n) (zpuNatToUnary n)
        (zpuNatToUnary_unary n)).val = BHist.Empty := by
  intro n
  induction n with
  | zero =>
      exact zpLevel_zero_val_empty (zpPow p e 0)
  | succ n ih =>
      let N := zpuNatToUnary n
      let One := zpuNatToUnary 1
      let S := zpuNatToUnary (n + 1)
      have NUnary : UnaryHistory N := zpuNatToUnary_unary n
      have OneUnary : UnaryHistory One := zpuNatToUnary_unary 1
      have SUnary : UnaryHistory S := zpuNatToUnary_unary (n + 1)
      have leftRaw :
          PDvdNat p N
            ((zpPow p e n).trunc (BEDC.FKernel.Cont.append N One)
              (unary_append_closed NUnary OneUnary)).val :=
        zpLevel_zero_ext_PDvdNat (zpPow p e n) NUnary OneUnary ih
      have leftLayer :
          hsame (BEDC.FKernel.Cont.append N One) S :=
        zpuNatToUnary_succ_right_hsame n
      have left :
          PDvdNat p N ((zpPow p e n).trunc S SUnary).val :=
        PDvdNat_hsame_exponent_result leftRaw (hsame_refl N)
          (zpTrunc_level_hsame (zpPow p e n)
            (unary_append_closed NUnary OneUnary) SUnary leftLayer)
      have rightRaw :
          PDvdNat p One
            (e.trunc (BEDC.FKernel.Cont.append One N)
              (unary_append_closed OneUnary NUnary)).val :=
        zpLevel_zero_ext_PDvdNat e OneUnary NUnary h1
      have rightLayer :
          hsame (BEDC.FKernel.Cont.append One N) S :=
        zpuNatToUnary_succ_left_hsame n
      have right :
          PDvdNat p One (e.trunc S SUnary).val :=
        PDvdNat_hsame_exponent_result rightRaw (hsame_refl One)
          (zpTrunc_level_hsame e
            (unary_append_closed OneUnary NUnary) SUnary rightLayer)
      exact zpMul_level_empty_of_PDvdNat_product (zpPow p e n) e SUnary
        (zpuNatToUnary_natAdd n 1) left right

theorem error_pow_vanish_at_length {p N : BHist} (e : ZpInt p)
    (NUnary : UnaryHistory N)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) :
    (zpLevel (zpPow p e (bwordLength N)) N NUnary).val = BHist.Empty := by
  have standardSame : hsame (zpuNatToUnary (bwordLength N)) N :=
    zpu_natToUnary_hsame_of_length NUnary
  have exactLevel := error_pow_vanish e h1 (bwordLength N)
  have transport :
      hsame
        ((zpPow p e (bwordLength N)).trunc (zpuNatToUnary (bwordLength N))
          (zpuNatToUnary_unary (bwordLength N))).val
        ((zpPow p e (bwordLength N)).trunc N NUnary).val :=
    zpTrunc_level_hsame (zpPow p e (bwordLength N))
      (zpuNatToUnary_unary (bwordLength N)) NUnary standardSame
  exact hsame_trans (hsame_symm transport) exactLevel

theorem error_tail_vanish {p : BHist} (e : ZpInt p)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) {M i : Nat} :
    M ≤ i ->
      (zpLevel (zpPow p e i) (zpuNatToUnary M)
        (zpuNatToUnary_unary M)).val = BHist.Empty := by
  intro leMI
  cases Nat.le.dest leMI with
  | intro tailNat sumEq =>
      let mLevel := zpuNatToUnary M
      let tail := zpuNatToUnary tailNat
      let iLevel := zpuNatToUnary i
      have mUnary : UnaryHistory mLevel := zpuNatToUnary_unary M
      have tailUnary : UnaryHistory tail := zpuNatToUnary_unary tailNat
      have iUnary : UnaryHistory iLevel := zpuNatToUnary_unary i
      have sameAppendI : hsame (BEDC.FKernel.Cont.append mLevel tail) iLevel := by
        have addSame := zpuNatToUnary_add_hsame M tailNat
        have sumSame : hsame (zpuNatToUnary (M + tailNat)) iLevel :=
          zpu_hsame_of_unary_length
            (zpuNatToUnary_unary (M + tailNat)) iUnary
            (by
              rw [zpuNatToUnary_length, zpuNatToUnary_length]
              exact sumEq)
        exact hsame_trans addSame sumSame
      have exactLevel := error_pow_vanish e h1 i
      have atAppend :
          hsame
            ((zpPow p e i).trunc (BEDC.FKernel.Cont.append mLevel tail)
              (unary_append_closed mUnary tailUnary)).val
            BHist.Empty :=
        hsame_trans
          (zpTrunc_level_hsame (zpPow p e i)
            (unary_append_closed mUnary tailUnary) iUnary sameAppendI)
          exactLevel
      have drop :=
        zp_trunc_drop_nat (zpPow p e i) mUnary tailUnary
      have modEmpty :
          hsame
            (natModFn (pPowCanon p mLevel)
              ((zpPow p e i).trunc (BEDC.FKernel.Cont.append mLevel tail)
                (unary_append_closed mUnary tailUnary)).val)
            BHist.Empty :=
        hsame_trans
          (natModFn_hsame_arg_transport (M := pPowCanon p mLevel) atAppend)
          (hsame_refl BHist.Empty)
      exact hsame_trans (hsame_symm drop) modEmpty

theorem zpAdd_level_zero_right {p N : BHist} (x y : ZpInt p)
    (NUnary : UnaryHistory N) :
    (y.trunc N NUnary).val = BHist.Empty ->
      hsame ((zpAdd p x y).trunc N NUnary).val (x.trunc N NUnary).val := by
  intro yZero
  unfold zpAdd zpAddTrunc fromNatModPow natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have raw :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val
            (y.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val BHist.Empty)) :=
    natModFn_append_hsame_transport (hsame_refl _) yZero
  have dropEmpty :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val BHist.Empty))
        (natModFn (pPowCanon p N) (x.trunc N NUnary).val) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (append_empty_right (x.trunc N NUnary).val)
  have reduceSelf :
      hsame (natModFn (pPowCanon p N) (x.trunc N NUnary).val)
        (x.trunc N NUnary).val :=
    natModFn_of_strict MUnary MNonempty xUnary (x.trunc N NUnary).isLt
  exact hsame_trans raw (hsame_trans dropEmpty reduceSelf)

theorem zpAdd_right_neg_cancel {p : BHist} (x z : ZpInt p) :
    ZpEq (zpAdd p (zpAdd p x z) (zpNeg p z)) x := by
  exact ZpEq_trans (zpAdd_assoc p x z (zpNeg p z))
    (ZpEq_trans
      (zpAdd_congr (ZpEq_refl x) (zpAdd_neg_right p z))
      (zpZero_add_right p z.prime x))

theorem zpAdd_cancel_right {p : BHist} {x y z : ZpInt p} :
    ZpEq (zpAdd p x z) (zpAdd p y z) -> ZpEq x y := by
  intro same
  exact ZpEq_trans
    (ZpEq_symm (zpAdd_right_neg_cancel x z))
    (ZpEq_trans
      (zpAdd_congr same (ZpEq_refl (zpNeg p z)))
      (zpAdd_right_neg_cancel y z))

theorem zpSub_add_cancel {p : BHist} (x y : ZpInt p) :
    ZpEq (zpAdd p (zpSub p y x) x) y := by
  unfold zpSub
  exact ZpEq_trans (zpAdd_assoc p y (zpNeg p x) x)
    (ZpEq_trans
      (zpAdd_congr (ZpEq_refl y) (zpAdd_neg_left p x))
      (zpZero_add_right p x.prime y))

theorem zpAdd_sub_cancel {p : BHist} (x y : ZpInt p) :
    ZpEq (zpAdd p x (zpSub p y x)) y := by
  unfold zpSub
  exact ZpEq_trans
    (ZpEq_symm (zpAdd_assoc p x y (zpNeg p x)))
    (ZpEq_trans
      (zpAdd_congr (zpAdd_comm p x y) (ZpEq_refl (zpNeg p x)))
      (ZpEq_trans
        (zpAdd_assoc p y x (zpNeg p x))
        (ZpEq_trans
          (zpAdd_congr (ZpEq_refl y) (zpAdd_neg_right p x))
          (zpZero_add_right p x.prime y))))

theorem zpSub_level_zero_right {p N : BHist} (x y : ZpInt p)
    (NUnary : UnaryHistory N) :
    (y.trunc N NUnary).val = BHist.Empty ->
      hsame ((zpSub p x y).trunc N NUnary).val (x.trunc N NUnary).val := by
  intro yZero
  have addDrop :
      hsame ((zpAdd p (zpNeg p y) y).trunc N NUnary).val
        ((zpNeg p y).trunc N NUnary).val :=
    zpAdd_level_zero_right (zpNeg p y) y NUnary yZero
  have negAddZero :
      hsame ((zpAdd p (zpNeg p y) y).trunc N NUnary).val
        ((zpZero p y.prime).trunc N NUnary).val :=
    zpAdd_neg_left p y N NUnary
  have negZero :
      ((zpNeg p y).trunc N NUnary).val = BHist.Empty :=
    hsame_trans (hsame_symm addDrop) negAddZero
  unfold zpSub
  exact zpAdd_level_zero_right x (zpNeg p y) NUnary negZero

theorem zpSub_mul_add_tail {p : BHist} (x y z : ZpInt p) :
    ZpEq (zpAdd p (zpMul p (zpSub p y x) z) (zpMul p z x))
      (zpMul p y z) := by
  have commuteTail :
      ZpEq (zpMul p z x) (zpMul p x z) :=
    zpMul_comm p z x
  have combine :
      ZpEq
        (zpAdd p (zpMul p (zpSub p y x) z) (zpMul p x z))
        (zpMul p (zpAdd p (zpSub p y x) x) z) :=
    ZpEq_symm (zpMul_add_distrib_right p (zpSub p y x) x z)
  exact ZpEq_trans
    (zpAdd_congr (ZpEq_refl _) commuteTail)
    (ZpEq_trans combine
      (zpMul_left_congr (zpSub_add_cancel x y)))

theorem zpSub_sub_cancel {p : BHist} (x y : ZpInt p) :
    ZpEq (zpSub p y (zpSub p y x)) x := by
  apply zpAdd_cancel_right (z := zpSub p y x)
  exact ZpEq_trans (zpSub_add_cancel (zpSub p y x) y)
    (ZpEq_symm (zpAdd_sub_cancel x y))

theorem zpOne_prime_irrel {p : BHist} (prime prime' : NatPrime p) :
    ZpEq (zpOne p prime) (zpOne p prime') := by
  intro N NUnary
  rfl

theorem zpGeom_step_core {p : BHist} (e P : ZpInt p) :
    ZpEq
      (zpAdd p
        (zpSub p (zpOne p e.prime) P)
        (zpMul p (zpSub p (zpOne p e.prime) e) P))
      (zpSub p (zpOne p e.prime) (zpMul p P e)) := by
  let O := zpOne p e.prime
  let PE := zpMul p P e
  apply zpAdd_cancel_right (z := PE)
  have leftAssoc :
      ZpEq
        (zpAdd p
          (zpAdd p
            (zpSub p O P)
            (zpMul p (zpSub p O e) P))
          PE)
        (zpAdd p
          (zpSub p O P)
          (zpAdd p (zpMul p (zpSub p O e) P) PE)) :=
    zpAdd_assoc p (zpSub p O P) (zpMul p (zpSub p O e) P) PE
  have tail :
      ZpEq (zpAdd p (zpMul p (zpSub p O e) P) PE) P := by
    exact ZpEq_trans (zpSub_mul_add_tail e O P)
      (zpOne_mul_left p e.prime P)
  have leftToO :
      ZpEq
        (zpAdd p
          (zpAdd p
            (zpSub p O P)
            (zpMul p (zpSub p O e) P))
          PE)
        O :=
    ZpEq_trans leftAssoc
      (ZpEq_trans
        (zpAdd_congr (ZpEq_refl (zpSub p O P)) tail)
        (zpSub_add_cancel P O))
  have rightToO :
      ZpEq (zpAdd p (zpSub p O PE) PE) O :=
    zpSub_add_cancel PE O
  exact ZpEq_trans leftToO (ZpEq_symm rightToO)

theorem zpGeom_identity {p : BHist} (e : ZpInt p) :
    ∀ n : Nat,
      ZpEq
        (zpMul p (zpSub p (zpOne p e.prime) e) (zpGeom p e n))
        (zpSub p (zpOne p e.prime) (zpPow p e n)) := by
  intro n
  induction n with
  | zero =>
      unfold zpGeom zpPow
      exact ZpEq_trans
        (zpMul_zero_right p (zpSub p (zpOne p e.prime) e))
        (ZpEq_symm (ZpEq_trans
          (by
            unfold zpSub
            exact zpAdd_neg_right p (zpOne p e.prime))
          (zpZero_prime_irrel (zpOne p e.prime).prime
            (zpSub p (zpOne p e.prime) e).prime)))
  | succ n ih =>
      let O := zpOne p e.prime
      let D := zpSub p O e
      let G := zpGeom p e n
      let P := zpPow p e n
      change ZpEq (zpMul p D (zpAdd p G P))
        (zpSub p O (zpMul p P e))
      exact ZpEq_trans
        (zpMul_add_distrib p D G P)
        (ZpEq_trans
          (zpAdd_congr ih (ZpEq_refl (zpMul p D P)))
          (zpGeom_step_core e P))

theorem zpGeomSeries_compat {p : BHist} (e : ZpInt p)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) :
    ZpCompatible p e.prime
      (fun N NUnary => (zpGeom p e (bwordLength N)).trunc N NUnary) := by
  intro N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod
  have nextCompat := (zpGeom p e (bwordLength (BHist.e1 N))).compat N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod at nextCompat
  have step :
      hsame
        ((zpGeom p e (bwordLength (BHist.e1 N))).trunc N NUnary).val
        ((zpGeom p e (bwordLength N)).trunc N NUnary).val := by
    change hsame
      ((zpGeom p e (bwordLength N + 1)).trunc N NUnary).val
      ((zpGeom p e (bwordLength N)).trunc N NUnary).val
    change hsame
      ((zpAdd p (zpGeom p e (bwordLength N)) (zpPow p e (bwordLength N))).trunc
        N NUnary).val
      ((zpGeom p e (bwordLength N)).trunc N NUnary).val
    exact zpAdd_level_zero_right (zpGeom p e (bwordLength N))
      (zpPow p e (bwordLength N)) NUnary
      (error_pow_vanish_at_length e NUnary h1)
  exact hsame_trans nextCompat step

def zpGeomSeries {p : BHist} (e : ZpInt p)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) : ZpInt p :=
  { prime := e.prime
    trunc := fun N NUnary => (zpGeom p e (bwordLength N)).trunc N NUnary
    compat := zpGeomSeries_compat e h1 }

theorem zpGeomSeries_mul_eq_one {p : BHist} (e : ZpInt p)
    (h1 : (zpLevel e (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty) :
    ZpEq
      (zpMul p (zpSub p (zpOne p e.prime) e) (zpGeomSeries e h1))
      (zpOne p e.prime) := by
  intro N NUnary
  change hsame
    ((zpMul p (zpSub p (zpOne p e.prime) e)
      (zpGeom p e (bwordLength N))).trunc N NUnary).val
    ((zpOne p e.prime).trunc N NUnary).val
  have finite := zpGeom_identity e (bwordLength N) N NUnary
  have tail :
      hsame
        ((zpSub p (zpOne p e.prime) (zpPow p e (bwordLength N))).trunc
          N NUnary).val
        ((zpOne p e.prime).trunc N NUnary).val :=
    zpSub_level_zero_right (zpOne p e.prime) (zpPow p e (bwordLength N))
      NUnary (error_pow_vanish_at_length e NUnary h1)
  exact hsame_trans finite tail

theorem zpSub_level_zero_of_level_eq {p N : BHist}
    (x y : ZpInt p) (NUnary : UnaryHistory N) :
    hsame (x.trunc N NUnary).val (y.trunc N NUnary).val ->
      (zpLevel (zpSub p x y) N NUnary).val = BHist.Empty := by
  intro sameXY
  unfold zpSub zpLevel zpAdd zpAddTrunc zpNeg zpNegTrunc fromNatModPow natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have compUnary :
      UnaryHistory (natComplementMod (pPowCanon p N) (y.trunc N NUnary).val) :=
    natComplementMod_unary MUnary
  have rawZero :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (y.trunc N NUnary).val
            (natComplementMod (pPowCanon p N) (y.trunc N NUnary).val)))
        BHist.Empty :=
    natComplementMod_add_left_zero_of_strict MUnary MNonempty yUnary
      (y.trunc N NUnary).isLt
  have transportToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val
            (natModFn (pPowCanon p N)
              (natComplementMod (pPowCanon p N) (y.trunc N NUnary).val))))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (y.trunc N NUnary).val
            (natComplementMod (pPowCanon p N) (y.trunc N NUnary).val))) := by
    exact natModFn_add_congruence MUnary MNonempty
      xUnary
      (natModFn_unary MUnary compUnary MNonempty)
      yUnary compUnary
      (hsame_trans
        (natModFn_of_strict MUnary MNonempty xUnary (x.trunc N NUnary).isLt)
        (hsame_trans sameXY
          (hsame_symm
            (natModFn_of_strict MUnary MNonempty yUnary (y.trunc N NUnary).isLt))))
      (mod_idem MUnary MNonempty compUnary)
  exact hsame_trans transportToRaw rawZero

theorem natModFn_hsame_mod_transport {M M' a : BHist} :
    hsame M M' -> hsame (natModFn M a) (natModFn M' a) := by
  intro same
  cases same
  rfl

theorem ZpUnitError_level_one {p : BHist} (a : ZpInt p) (unit : ZpUnit a) :
    (zpLevel (ZpUnitError a unit) (zpuNatToUnary 1)
      (zpuNatToUnary_unary 1)).val = BHist.Empty := by
  change (zpLevel (ZpUnitError a unit) (BHist.e1 BHist.Empty)
    (unary_e1_closed unary_empty)).val = BHist.Empty
  unfold ZpUnitError
  apply zpSub_level_zero_of_level_eq
  unfold zpOne zpMul zpMulTrunc fromNatModPow natMod
  have onePowerSame := pPowCanon_one_hsame a.prime
  have seedMod := ZpUnitSeedInv_mod_p a unit
  change hsame
    (natModFn (pPowCanon p (BHist.e1 BHist.Empty)) NatOne)
    (natModFn (pPowCanon p (BHist.e1 BHist.Empty))
      (natMulFn
        (zpLevel a (BHist.e1 BHist.Empty) (unary_e1_closed unary_empty)).val
        (zpLevel (ZpUnitSeedInv a unit) (BHist.e1 BHist.Empty)
          (unary_e1_closed unary_empty)).val))
  exact hsame_trans
    (natModFn_hsame_mod_transport onePowerSame)
    (hsame_trans (hsame_symm seedMod)
      (hsame_symm (natModFn_hsame_mod_transport onePowerSame)))

def ZpUnitInv {p : BHist} (a : ZpInt p) (unit : ZpUnit a) : ZpInt p :=
  let e := ZpUnitError a unit
  zpMul p (ZpUnitSeedInv a unit)
    (zpGeomSeries e (ZpUnitError_level_one a unit))

theorem ZpUnitInv_mul {p : BHist} (a : ZpInt p) (unit : ZpUnit a) :
    ZpEq (zpMul p a (ZpUnitInv a unit)) (zpOne p a.prime) := by
  let b := ZpUnitSeedInv a unit
  let e := ZpUnitError a unit
  let g := zpGeomSeries e (ZpUnitError_level_one a unit)
  have abGeom :
      ZpEq (zpMul p a (ZpUnitInv a unit))
        (zpMul p (zpMul p a b) g) := by
    unfold ZpUnitInv
    change ZpEq (zpMul p a (zpMul p b g)) (zpMul p (zpMul p a b) g)
    exact ZpEq_symm (zpMul_assoc p a b g)
  have oneMinusError :
      ZpEq (zpMul p a b) (zpSub p (zpOne p a.prime) e) := by
    unfold e ZpUnitError
    exact ZpEq_symm
      (zpSub_sub_cancel (zpMul p a b) (zpOne p a.prime))
  have replace :
      ZpEq (zpMul p (zpMul p a b) g)
        (zpMul p (zpSub p (zpOne p a.prime) e) g) :=
    zpMul_left_congr oneMinusError
  exact ZpEq_trans abGeom
    (ZpEq_trans replace
      (zpGeomSeries_mul_eq_one e (ZpUnitError_level_one a unit)))

theorem ZpUnitInv_mul_right {p : BHist} (a : ZpInt p) (unit : ZpUnit a) :
    ZpEq (zpMul p (ZpUnitInv a unit) a) (zpOne p a.prime) := by
  exact ZpEq_trans (zpMul_comm p (ZpUnitInv a unit) a)
    (ZpUnitInv_mul a unit)

end BEDC.Derived.PadicUp
