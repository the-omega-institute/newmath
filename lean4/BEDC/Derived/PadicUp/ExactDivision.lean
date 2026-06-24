import BEDC.Derived.PadicUp.FieldCore

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

theorem natQuotFn_unary {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      UnaryHistory (natQuotFn M n) := by
  intro MUnary nUnary MNonempty
  exact NatDivRem_quotient_unary (natModFn_spec MUnary nUnary MNonempty)

theorem natDivRem_zero_recompose {M n : BHist}
    (MUnary : UnaryHistory M) (nUnary : UnaryHistory n)
    (MNonempty : hsame M BHist.Empty -> False) :
    hsame (natModFn M n) BHist.Empty ->
      hsame (natMulFn M (natQuotFn M n)) n := by
  intro remZero
  have divrem := natModFn_spec MUnary nUnary MNonempty
  cases divrem with
  | intro mq data =>
      have productSame : hsame mq (natMulFn M (natQuotFn M n)) :=
        NatMul_functional MUnary data.left
          (natMulFn_rel MUnary (NatDivRem_quotient_unary ⟨mq, data⟩))
      have display : Cont mq BHist.Empty n :=
        cont_hsame_transport (hsame_refl mq) remZero (hsame_refl n)
          data.right.left.right.right
      have mqSameN : hsame mq n :=
        hsame_symm (Iff.mp cont_right_unit_iff display)
      exact hsame_trans (hsame_symm productSame) mqSameN

theorem natDivRem_zero_recompose_comm {M n : BHist}
    (MUnary : UnaryHistory M) (nUnary : UnaryHistory n)
    (MNonempty : hsame M BHist.Empty -> False) :
    hsame (natModFn M n) BHist.Empty ->
      hsame (natMulFn (natQuotFn M n) M) n := by
  intro remZero
  have left := natDivRem_zero_recompose MUnary nUnary MNonempty remZero
  have qUnary : UnaryHistory (natQuotFn M n) :=
    natQuotFn_unary MUnary nUnary MNonempty
  exact hsame_trans
    (natMulFn_comm_hsame qUnary MUnary)
    left

theorem natQuotFn_mul_exact {D q n : BHist}
    (DUnary : UnaryHistory D) (DNonempty : hsame D BHist.Empty -> False)
    (_qUnary : UnaryHistory q) :
    NatMul D q n -> hsame (natQuotFn D n) q := by
  intro product
  have nUnary : UnaryHistory n := NatMul_result_unary DUnary product
  have divrem : NatDivRem D n q BHist.Empty :=
    ⟨n, product,
      And.intro nUnary (And.intro unary_empty (cont_right_unit n)),
      NatUnary_nonempty_positive_for_divides_closure DUnary DNonempty⟩
  exact (natModFn_unique DUnary nUnary DNonempty divrem).left

theorem NatMul_assoc_left_exact {D M q K mq kq : BHist}
    (DUnary : UnaryHistory D) (MUnary : UnaryHistory M) (qUnary : UnaryHistory q)
    (productDM : NatMul D M K) (productMQ : NatMul M q mq)
    (productKQ : NatMul K q kq) :
    NatMul D mq kq := by
  have mqUnary : UnaryHistory mq := NatMul_result_unary MUnary productMQ
  have total := NatMul_total DUnary mqUnary
  cases total with
  | intro displayed displayedData =>
      have sameDisplayed :
          hsame kq displayed :=
        NatMul_assoc_hsame DUnary MUnary qUnary productDM productKQ
          productMQ displayedData.right
      exact (NatMul_result_hsame_transport displayedData.right
        (hsame_symm sameDisplayed)).right

theorem append_hsame_transport {a b c d : BHist} :
    hsame a b -> hsame c d ->
      hsame (BEDC.FKernel.Cont.append a c) (BEDC.FKernel.Cont.append b d) := by
  intro sameA sameC
  cases sameA
  cases sameC
  rfl

theorem natQuotFn_hsame_arg_transport {M a b : BHist} :
    hsame a b -> hsame (natQuotFn M a) (natQuotFn M b) := by
  intro same
  cases same
  rfl

theorem natModFn_add_left_divisible_drop {M x y : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (xUnary : UnaryHistory x) (yUnary : UnaryHistory y) :
    NatDivides M x ->
      hsame (natModFn M (BEDC.FKernel.Cont.append x y)) (natModFn M y) := by
  intro dividesX
  have xZero :
      hsame (natModFn M x) BHist.Empty :=
    (dvd_iff_mod_zero MUnary MNonempty xUnary).mp dividesX
  have ySelf :
      hsame (natModFn M y) (natModFn M y) :=
    hsame_refl _
  have raw :
      hsame (natModFn M (BEDC.FKernel.Cont.append x y))
        (natModFn M (BEDC.FKernel.Cont.append BHist.Empty y)) :=
    natModFn_add_congruence MUnary MNonempty xUnary yUnary unary_empty yUnary
      xZero ySelf
  exact hsame_trans raw
    (natModFn_hsame_arg_transport (M := M) (append_empty_left y))

theorem quot_mod_tower_compat {D M K n : BHist}
    (DUnary : UnaryHistory D) (MUnary : UnaryHistory M) (KUnary : UnaryHistory K)
    (nUnary : UnaryHistory n)
    (DNonempty : hsame D BHist.Empty -> False)
    (MNonempty : hsame M BHist.Empty -> False)
    (KNonempty : hsame K BHist.Empty -> False)
    (productDM : NatMul D M K) :
    NatDivides D n ->
      hsame (natModFn M (natQuotFn D n))
        (natModFn M (natQuotFn D (natModFn K n))) := by
  intro dividesN
  let qK := natQuotFn K n
  let rK := natModFn K n
  let qD := natQuotFn D n
  let qPrefix := natQuotFn D (natMulFn K qK)
  let qR := natQuotFn D rK
  have divremK : NatDivRem K n qK rK :=
    natModFn_spec KUnary nUnary KNonempty
  have qKUnary : UnaryHistory qK :=
    NatDivRem_quotient_unary divremK
  have rKUnary : UnaryHistory rK :=
    NatDivRem_remainder_unary divremK
  have kqUnary : UnaryHistory (natMulFn K qK) :=
    natMulFn_unary KUnary qKUnary
  have dividesK : NatDivides D K :=
    ⟨M, MUnary, productDM⟩
  have dividesKq : NatDivides D (natMulFn K qK) :=
    NatDivides_mul_right_factor_closed qKUnary dividesK
      (natMulFn_rel KUnary qKUnary)
  have dividesRK : NatDivides D rK := by
    cases divremK with
    | intro mq data =>
        have sameProduct :
            hsame mq (natMulFn K qK) :=
          NatMul_functional KUnary data.left
            (natMulFn_rel KUnary qKUnary)
        have dividesMq : NatDivides D mq :=
          (NatDivides_dividend_hsame_transport dividesKq
            (hsame_symm sameProduct)).right
        exact dvd_tail_of_dvd_sum DUnary DNonempty data.right.left
          dividesMq dividesN
  have remD_N :
      hsame (natModFn D n) BHist.Empty :=
    (dvd_iff_mod_zero DUnary DNonempty nUnary).mp dividesN
  have remD_Kq :
      hsame (natModFn D (natMulFn K qK)) BHist.Empty :=
    (dvd_iff_mod_zero DUnary DNonempty kqUnary).mp dividesKq
  have remD_R :
      hsame (natModFn D rK) BHist.Empty :=
    (dvd_iff_mod_zero DUnary DNonempty rKUnary).mp dividesRK
  have qPrefixProduct :
      hsame qPrefix (natMulFn M qK) := by
    have productMQ : NatMul M qK (natMulFn M qK) :=
      natMulFn_rel MUnary qKUnary
    have productDKq :
        NatMul D (natMulFn M qK) (natMulFn K qK) :=
      NatMul_assoc_left_exact DUnary MUnary qKUnary productDM productMQ
        (natMulFn_rel KUnary qKUnary)
    exact natQuotFn_mul_exact DUnary DNonempty
      (natMulFn_unary MUnary qKUnary) productDKq
  have qPrefixDividesM : NatDivides M qPrefix := by
    have raw : NatDivides M (natMulFn M qK) :=
      ⟨qK, qKUnary, natMulFn_rel MUnary qKUnary⟩
    exact (NatDivides_dividend_hsame_transport raw
      (hsame_symm qPrefixProduct)).right
  have qPrefixUnary : UnaryHistory qPrefix :=
    natQuotFn_unary DUnary kqUnary DNonempty
  have qRUnary : UnaryHistory qR :=
    natQuotFn_unary DUnary rKUnary DNonempty
  have qDUnary : UnaryHistory qD :=
    natQuotFn_unary DUnary nUnary DNonempty
  have productPrefix :
      hsame (natMulFn D qPrefix) (natMulFn K qK) :=
    natDivRem_zero_recompose DUnary kqUnary DNonempty remD_Kq
  have productR :
      hsame (natMulFn D qR) rK :=
    natDivRem_zero_recompose DUnary rKUnary DNonempty remD_R
  have productDAppend :
      NatMul D (BEDC.FKernel.Cont.append qPrefix qR)
        (BEDC.FKernel.Cont.append (natMulFn D qPrefix) (natMulFn D qR)) :=
    NatMul_append_cont
      (natMulFn_rel DUnary qPrefixUnary)
      (natMulFn_rel DUnary qRUnary)
      (cont_intro rfl)
  have appendProductSame :
      hsame (BEDC.FKernel.Cont.append (natMulFn D qPrefix) (natMulFn D qR)) n := by
    cases divremK with
    | intro mq data =>
        have sameLeft :
            hsame (natMulFn D qPrefix) mq :=
          hsame_trans productPrefix
            (hsame_symm
              (NatMul_functional KUnary data.left
                (natMulFn_rel KUnary qKUnary)))
        have sameRight : hsame (natMulFn D qR) rK := productR
        have sameAppend :
            hsame (BEDC.FKernel.Cont.append (natMulFn D qPrefix) (natMulFn D qR))
              (BEDC.FKernel.Cont.append mq rK) :=
          append_hsame_transport sameLeft sameRight
        exact hsame_trans sameAppend (hsame_symm data.right.left.right.right)
  have productDAppendN :
      NatMul D (BEDC.FKernel.Cont.append qPrefix qR) n :=
    (NatMul_result_hsame_transport productDAppend appendProductSame).right
  have divremD :
      NatDivRem D n (BEDC.FKernel.Cont.append qPrefix qR) BHist.Empty :=
    ⟨n, productDAppendN,
      And.intro nUnary (And.intro unary_empty (cont_right_unit n)),
      NatUnary_nonempty_positive_for_divides_closure DUnary DNonempty⟩
  have qDAppend :
      hsame qD (BEDC.FKernel.Cont.append qPrefix qR) :=
    (natModFn_unique DUnary nUnary DNonempty divremD).left
  have leftDrop :
      hsame (natModFn M qD)
        (natModFn M (BEDC.FKernel.Cont.append qPrefix qR)) :=
    natModFn_hsame_arg_transport (M := M) qDAppend
  have prefixDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append qPrefix qR))
        (natModFn M qR) :=
    natModFn_add_left_divisible_drop MUnary MNonempty
      qPrefixUnary qRUnary qPrefixDividesM
  exact hsame_trans leftDrop prefixDrop
theorem pPowCanon_append_mul {p N K : BHist}
    (prime : NatPrime p) (NUnary : UnaryHistory N) (KUnary : UnaryHistory K) :
    hsame (pPowCanon p (BEDC.FKernel.Cont.append N K))
      (natMulFn (pPowCanon p K) (pPowCanon p N)) := by
  let NK := BEDC.FKernel.Cont.append N K
  have NKUnary : UnaryHistory NK := unary_append_closed NUnary KUnary
  have powN := pPowCanon_PPow prime.left NUnary
  have powK := pPowCanon_PPow prime.left KUnary
  have powNK := pPowCanon_PPow prime.left NKUnary
  have add : NatAdd N K NK := ⟨NUnary, KUnary, rfl⟩
  have rawMul :
      NatMul (pPowCanon p N) (pPowCanon p K)
        (natMulFn (pPowCanon p N) (pPowCanon p K)) :=
    natMulFn_rel (pPowCanon_unary p N) (pPowCanon_unary p K)
  have rawPow :
      PPow p NK (natMulFn (pPowCanon p N) (pPowCanon p K)) :=
    PPow_add powN powK add rawMul
  have sameRaw :
      hsame (natMulFn (pPowCanon p N) (pPowCanon p K)) (pPowCanon p NK) :=
    PPow_functional rawPow powNK
  have comm :
      hsame (natMulFn (pPowCanon p K) (pPowCanon p N))
        (natMulFn (pPowCanon p N) (pPowCanon p K)) :=
    natMulFn_comm_hsame (pPowCanon_unary p K) (pPowCanon_unary p N)
  exact hsame_symm (hsame_trans comm sameRaw)

theorem zpLevel_zero_to_pow_dvd {p : BHist} (a : ZpInt p)
    (k : Nat)
    (zeroK :
      (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty) :
    ∀ N : Nat,
      NatDivides (pPowCanon p (zpuNatToUnary k))
        (zpLevel a (zpuNatToUnary (N + k))
          (zpuNatToUnary_unary (N + k))).val := by
  intro N
  let K := zpuNatToUnary k
  let T := zpuNatToUnary N
  let NK := zpuNatToUnary (N + k)
  have KUnary : UnaryHistory K := zpuNatToUnary_unary k
  have TUnary : UnaryHistory T := zpuNatToUnary_unary N
  have raw :
      NatDivides (pPowCanon p K)
        (a.trunc (BEDC.FKernel.Cont.append K T)
          (unary_append_closed KUnary TUnary)).val :=
    zpLevel_zero_ext_dvd a KUnary TUnary zeroK
  have sameLayer : hsame (BEDC.FKernel.Cont.append K T) NK := by
    have addSame := zpuNatToUnary_add_hsame k N
    have sumSame : hsame (zpuNatToUnary (k + N)) NK :=
      zpu_hsame_of_unary_length (zpuNatToUnary_unary (k + N))
        (zpuNatToUnary_unary (N + k))
        (by rw [zpuNatToUnary_length, zpuNatToUnary_length, Nat.add_comm])
    exact hsame_trans addSame sumSame
  exact (NatDivides_dividend_hsame_transport raw
    (zpTrunc_level_hsame a (unary_append_closed KUnary TUnary)
      (zpuNatToUnary_unary (N + k)) sameLayer)).right

def divPowExactTrunc {p : BHist} (a : ZpInt p) (k : Nat)
    (N : BHist) (NUnary : UnaryHistory N) : ZpTrunc p N :=
  fromNatModPow p N
    (natQuotFn (pPowCanon p (zpuNatToUnary k))
      (a.trunc (BEDC.FKernel.Cont.append N (zpuNatToUnary k))
        (unary_append_closed NUnary (zpuNatToUnary_unary k))).val)
    a.prime NUnary

theorem divPowExact_bound {p : BHist} (a : ZpInt p) (k : Nat)
    (N : BHist) (NUnary : UnaryHistory N) :
    NatUnaryStrictPrefix (divPowExactTrunc a k N NUnary).val (pPowCanon p N) := by
  exact (divPowExactTrunc a k N NUnary).isLt

theorem divPowExact_value_compat {p : BHist} (a : ZpInt p) (k : Nat)
    (zeroK :
      (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty)
    (N : BHist) (NUnary : UnaryHistory N) :
    hsame
      (reduce p N a.prime NUnary
        (divPowExactTrunc a k (BHist.e1 N) (unary_e1_closed NUnary))).val
      (divPowExactTrunc a k N NUnary).val := by
  let K := zpuNatToUnary k
  let D := pPowCanon p K
  let M := pPowCanon p N
  let N1 := BHist.e1 N
  let NK := BEDC.FKernel.Cont.append N K
  let high := BEDC.FKernel.Cont.append N1 K
  let nHigh := (a.trunc high
    (unary_append_closed (unary_e1_closed NUnary) (zpuNatToUnary_unary k))).val
  let nLow := (a.trunc NK
    (unary_append_closed NUnary (zpuNatToUnary_unary k))).val
  change hsame
    (natModFn M
      (natModFn (pPowCanon p N1)
        (natQuotFn D nHigh)))
    (natModFn M (natQuotFn D nLow))
  have KUnary : UnaryHistory K := zpuNatToUnary_unary k
  have N1Unary : UnaryHistory N1 := unary_e1_closed NUnary
  have NKUnary : UnaryHistory NK := unary_append_closed NUnary KUnary
  have highUnary : UnaryHistory high := unary_append_closed N1Unary KUnary
  have DUnary : UnaryHistory D := pPowCanon_unary p K
  have MUnary : UnaryHistory M := pPowCanon_unary p N
  have P1Unary : UnaryHistory (pPowCanon p N1) := pPowCanon_unary p N1
  have PNKUnary : UnaryHistory (pPowCanon p NK) := pPowCanon_unary p NK
  have DNonempty : hsame D BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime KUnary
  have MNonempty : hsame M BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime NUnary
  have P1Nonempty : hsame (pPowCanon p N1) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime N1Unary
  have PNKNonempty : hsame (pPowCanon p NK) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime NKUnary
  have nHighUnary : UnaryHistory nHigh :=
    BoundedNat_unary (pPowCanon_unary p high)
      (a.trunc high highUnary)
  have qHighUnary : UnaryHistory (natQuotFn D nHigh) :=
    natQuotFn_unary DUnary nHighUnary DNonempty
  have dividesMP1 :
      NatDivides M (pPowCanon p N1) :=
    pow_dvd_pow_of_le a.prime NUnary N1Unary
      ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, rfl⟩
  have outerDrop :
      hsame
        (natModFn M
          (natModFn (pPowCanon p N1)
            (natQuotFn D nHigh)))
        (natModFn M (natQuotFn D nHigh)) :=
    natModFn_rem_rem_of_dvd MUnary MNonempty P1Unary P1Nonempty
      qHighUnary dividesMP1
  have productDM : NatMul D M (pPowCanon p NK) := by
    have productRaw : NatMul D M (natMulFn D M) :=
      natMulFn_rel DUnary MUnary
    have powerSame : hsame (pPowCanon p NK) (natMulFn D M) :=
      pPowCanon_append_mul a.prime NUnary KUnary
    exact (NatMul_result_hsame_transport productRaw (hsame_symm powerSame)).right
  have dividesHigh : NatDivides D nHigh := by
    have raw :
        NatDivides D
          (a.trunc (BEDC.FKernel.Cont.append K N1)
            (unary_append_closed KUnary N1Unary)).val :=
      zpLevel_zero_ext_dvd a KUnary N1Unary zeroK
    have sameLayer :
        hsame (BEDC.FKernel.Cont.append K N1) high :=
      unary_append_comm KUnary N1Unary
    exact (NatDivides_dividend_hsame_transport raw
      (zpTrunc_level_hsame a
        (unary_append_closed KUnary N1Unary) highUnary sameLayer)).right
  have quotientTower :
      hsame (natModFn M (natQuotFn D nHigh))
        (natModFn M (natQuotFn D (natModFn (pPowCanon p NK) nHigh))) :=
    quot_mod_tower_compat DUnary MUnary PNKUnary nHighUnary
      DNonempty MNonempty PNKNonempty productDM dividesHigh
  have highDrop :
      hsame (natModFn (pPowCanon p NK) nHigh) nLow := by
    let one := BHist.e1 BHist.Empty
    have oneUnary : UnaryHistory one := unary_e1_closed unary_empty
    have sameHigh :
        hsame high (BEDC.FKernel.Cont.append NK one) := by
      exact zpu_hsame_of_unary_length highUnary
        (unary_append_closed NKUnary oneUnary)
        (by
          unfold high N1 NK K one
          rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
          rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
          rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
          change Nat.succ (bwordLength N) + bwordLength (zpuNatToUnary k) =
            bwordLength N + bwordLength (zpuNatToUnary k) + 1
          rw [Nat.succ_eq_add_one]
          calc
            (bwordLength N + 1) + bwordLength (zpuNatToUnary k) =
                bwordLength N + (1 + bwordLength (zpuNatToUnary k)) :=
              Nat.add_assoc (bwordLength N) 1 (bwordLength (zpuNatToUnary k))
            _ = bwordLength N + (bwordLength (zpuNatToUnary k) + 1) := by
              rw [Nat.add_comm 1 (bwordLength (zpuNatToUnary k))]
            _ = bwordLength N + bwordLength (zpuNatToUnary k) + 1 := by
              rw [Nat.add_assoc])
    have levelTransport :
        hsame nHigh
          (a.trunc (BEDC.FKernel.Cont.append NK one)
            (unary_append_closed NKUnary oneUnary)).val :=
      zpTrunc_level_hsame a highUnary
        (unary_append_closed NKUnary oneUnary) sameHigh
    have modTransport :
        hsame (natModFn (pPowCanon p NK) nHigh)
          (natModFn (pPowCanon p NK)
            (a.trunc (BEDC.FKernel.Cont.append NK one)
              (unary_append_closed NKUnary oneUnary)).val) :=
      natModFn_hsame_arg_transport (M := pPowCanon p NK) levelTransport
    have dropOne :
        hsame
          (natModFn (pPowCanon p NK)
            (a.trunc (BEDC.FKernel.Cont.append NK one)
              (unary_append_closed NKUnary oneUnary)).val)
          nLow :=
      zp_trunc_drop_nat a NKUnary oneUnary
    exact hsame_trans modTransport dropOne
  have quotientTransport :
      hsame
        (natModFn M (natQuotFn D (natModFn (pPowCanon p NK) nHigh)))
        (natModFn M (natQuotFn D nLow)) :=
    natModFn_hsame_arg_transport (M := M)
      (natQuotFn_hsame_arg_transport highDrop)
  exact hsame_trans outerDrop
    (hsame_trans quotientTower quotientTransport)

theorem divPowExact_compat {p : BHist} (a : ZpInt p) (k : Nat)
    (zeroK :
      (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty) :
    ZpCompatible p a.prime (fun N NUnary => divPowExactTrunc a k N NUnary) := by
  intro N NUnary
  exact divPowExact_value_compat a k zeroK N NUnary

def zpDivPowExact {p : BHist} (a : ZpInt p) (k : Nat)
    (zeroK :
      (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty) :
    ZpInt p :=
  { prime := a.prime
    trunc := fun N NUnary => divPowExactTrunc a k N NUnary
    compat := divPowExact_compat a k zeroK }

theorem pow_mul_divPowExact {p : BHist} (a : ZpInt p) (k : Nat)
    (zeroK :
      (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val = BHist.Empty) :
    ZpEq (zpMul p (zpPowP p a.prime k) (zpDivPowExact a k zeroK)) a := by
  intro N NUnary
  let K := zpuNatToUnary k
  let D := pPowCanon p K
  let M := pPowCanon p N
  let NK := BEDC.FKernel.Cont.append N K
  let n := (a.trunc NK (unary_append_closed NUnary (zpuNatToUnary_unary k))).val
  unfold zpMul zpMulTrunc fromNatModPow natMod zpDivPowExact divPowExactTrunc
  change hsame
    (natModFn M
      (natMulFn ((zpPowP p a.prime k).trunc N NUnary).val
        (natModFn M (natQuotFn D n))))
    (a.trunc N NUnary).val
  have KUnary : UnaryHistory K := zpuNatToUnary_unary k
  have NKUnary : UnaryHistory NK := unary_append_closed NUnary KUnary
  have DUnary : UnaryHistory D := pPowCanon_unary p K
  have MUnary : UnaryHistory M := pPowCanon_unary p N
  have DNonempty : hsame D BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime KUnary
  have MNonempty : hsame M BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime a.prime NUnary
  have nUnary : UnaryHistory n :=
    BoundedNat_unary (pPowCanon_unary p NK)
      (a.trunc NK NKUnary)
  have qUnary : UnaryHistory (natQuotFn D n) :=
    natQuotFn_unary DUnary nUnary DNonempty
  have powerAtN :
      hsame ((zpPowP p a.prime k).trunc N NUnary).val
        (natModFn M D) :=
    (pPowZp_natToZp p a.prime k) N NUnary
  have replacePower :
      hsame
        (natModFn M
          (natMulFn ((zpPowP p a.prime k).trunc N NUnary).val
            (natModFn M (natQuotFn D n))))
        (natModFn M
          (natMulFn (natModFn M D)
            (natModFn M (natQuotFn D n)))) :=
    natModFn_hsame_arg_transport (M := M)
      (natMulFn_hsame_transport powerAtN (hsame_refl _))
  have reduceProduct :
      hsame
        (natModFn M
          (natMulFn (natModFn M D)
            (natModFn M (natQuotFn D n))))
        (natModFn M (natMulFn D (natQuotFn D n))) :=
    hsame_symm (mod_mul_compat MUnary MNonempty DUnary qUnary)
  have dividesN : NatDivides D n := by
    have raw :
        NatDivides D
          (a.trunc (BEDC.FKernel.Cont.append K N)
            (unary_append_closed KUnary NUnary)).val :=
      zpLevel_zero_ext_dvd a KUnary NUnary zeroK
    exact (NatDivides_dividend_hsame_transport raw
      (zpTrunc_level_hsame a
        (unary_append_closed KUnary NUnary) NKUnary
        (unary_append_comm KUnary NUnary))).right
  have remZero :
      hsame (natModFn D n) BHist.Empty :=
    (dvd_iff_mod_zero DUnary DNonempty nUnary).mp dividesN
  have recompose :
      hsame (natMulFn D (natQuotFn D n)) n :=
    natDivRem_zero_recompose DUnary nUnary DNonempty remZero
  have rawToN :
      hsame (natModFn M (natMulFn D (natQuotFn D n)))
        (natModFn M n) :=
    natModFn_hsame_arg_transport (M := M) recompose
  have drop :
      hsame (natModFn M n) (a.trunc N NUnary).val :=
    zp_trunc_drop_nat a NUnary KUnary
  exact hsame_trans replacePower
    (hsame_trans reduceProduct (hsame_trans rawToN drop))

theorem pow_mul_level_succ_zero_of_unit_zero {p : BHist} (prime : NatPrime p)
    (k : Nat) (z : ZpInt p)
    (unitZero :
      (zpLevel z (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val = BHist.Empty) :
    (zpLevel (zpMul p (zpPowP p prime k) z) (zpuNatToUnary (k + 1))
      (zpuNatToUnary_unary (k + 1))).val = BHist.Empty := by
  let K := zpuNatToUnary k
  let One := zpuNatToUnary 1
  let S := zpuNatToUnary (k + 1)
  have KUnary : UnaryHistory K := zpuNatToUnary_unary k
  have OneUnary : UnaryHistory One := zpuNatToUnary_unary 1
  have SUnary : UnaryHistory S := zpuNatToUnary_unary (k + 1)
  have leftLayer :
      PDvdNat p K ((zpPowP p prime k).trunc S SUnary).val := by
    have powerToNat := pPowZp_natToZp p prime k
    have powerValSame :
        hsame ((zpPowP p prime k).trunc S SUnary).val
          (natModFn (pPowCanon p S) (pPowCanon p K)) :=
      powerToNat S SUnary
    have powDividesSelf : NatDivides (pPowCanon p K) (pPowCanon p K) :=
      (NatDivides_reflexive_pair (pPowCanon_unary p K)).right
    have divisorOfS : NatDivides (pPowCanon p K) (pPowCanon p S) := by
      have sameLayer : hsame (BEDC.FKernel.Cont.append K One) S :=
        zpuNatToUnary_succ_right_hsame k
      have productSame :
          hsame (pPowCanon p S)
            (pPowCanon p (BEDC.FKernel.Cont.append K One)) :=
        pPowCanon_hsame_level (hsame_symm sameLayer)
      have productPower :
          hsame (pPowCanon p (BEDC.FKernel.Cont.append K One))
            (natMulFn (pPowCanon p One) (pPowCanon p K)) :=
        pPowCanon_append_mul prime KUnary OneUnary
      have rawDivides :
          NatDivides (pPowCanon p K)
            (natMulFn (pPowCanon p One) (pPowCanon p K)) := by
        have comm :
            hsame (natMulFn (pPowCanon p One) (pPowCanon p K))
              (natMulFn (pPowCanon p K) (pPowCanon p One)) :=
          natMulFn_comm_hsame (pPowCanon_unary p One) (pPowCanon_unary p K)
        have direct :
            NatDivides (pPowCanon p K)
              (natMulFn (pPowCanon p K) (pPowCanon p One)) :=
          ⟨pPowCanon p One, pPowCanon_unary p One,
            natMulFn_rel (pPowCanon_unary p K) (pPowCanon_unary p One)⟩
        exact (NatDivides_dividend_hsame_transport direct (hsame_symm comm)).right
      exact (NatDivides_dividend_hsame_transport rawDivides
        (hsame_symm (hsame_trans productSame productPower))).right
    have strictPower :
        NatUnaryStrictPrefix (pPowCanon p K) (pPowCanon p S) := by
      apply NatUnaryStrictPrefix_of_length_lt
      · exact pPowCanon_unary p K
      · exact pPowCanon_unary p S
      · rw [pPowCanon_length, pPowCanon_length]
        have pBeyondOne := NatUnaryStrictPrefix_length_lt
          (unary_e1_closed unary_empty) prime.right.left
        change bwordLength p ^ bwordLength K < bwordLength p ^ bwordLength S
        have oneLtP : 1 < bwordLength p := by
          simpa [BEDC.FKernel.ExternalBinary.bwordLength] using pBeyondOne
        have lengthStep : bwordLength S = bwordLength K + 1 := by
          unfold S K
          rw [zpuNatToUnary_length, zpuNatToUnary_length]
        rw [lengthStep]
        exact Nat.pow_lt_pow_succ oneLtP
    have modSame :
        hsame (natModFn (pPowCanon p S) (pPowCanon p K))
          (pPowCanon p K) :=
      natModFn_of_strict (pPowCanon_unary p S)
        (pPowCanon_nonempty_of_prime prime SUnary)
        (pPowCanon_unary p K) strictPower
    have modDivides :
        NatDivides (pPowCanon p K)
          (natModFn (pPowCanon p S) (pPowCanon p K)) :=
      (NatDivides_dividend_hsame_transport powDividesSelf
        (hsame_symm modSame)).right
    exact PDvdNat_hsame_exponent_result
      ⟨pPowCanon p K, pPowCanon_PPow prime.left KUnary, modDivides⟩
      (hsame_refl K) (hsame_symm powerValSame)
  have rightRaw :
      PDvdNat p One
        (z.trunc (BEDC.FKernel.Cont.append One K)
          (unary_append_closed OneUnary KUnary)).val :=
    zpLevel_zero_ext_PDvdNat z OneUnary KUnary unitZero
  have rightLayerSame :
      hsame (BEDC.FKernel.Cont.append One K) S :=
    zpuNatToUnary_succ_left_hsame k
  have rightLayer :
      PDvdNat p One (z.trunc S SUnary).val :=
    PDvdNat_hsame_exponent_result rightRaw (hsame_refl One)
      (zpTrunc_level_hsame z
        (unary_append_closed OneUnary KUnary) SUnary rightLayerSame)
  exact zpMul_level_empty_of_PDvdNat_product (zpPowP p prime k) z SUnary
    (zpuNatToUnary_natAdd k 1) leftLayer rightLayer

theorem divPowExact_unit {p : BHist} {a : ZpInt p} (w : ZpValWitness a) :
    ZpUnit (zpDivPowExact a w.k w.zero_k) := by
  unfold ZpUnit
  intro unitZero
  have scaledZero :
      (zpLevel
        (zpMul p (zpPowP p a.prime w.k)
          (zpDivPowExact a w.k w.zero_k))
        (zpuNatToUnary (w.k + 1)) (zpuNatToUnary_unary (w.k + 1))).val =
        BHist.Empty :=
    pow_mul_level_succ_zero_of_unit_zero a.prime w.k
      (zpDivPowExact a w.k w.zero_k) unitZero
  have exactEq :=
    pow_mul_divPowExact a w.k w.zero_k
  have transport :
      hsame
        ((zpMul p (zpPowP p a.prime w.k)
          (zpDivPowExact a w.k w.zero_k)).trunc
          (zpuNatToUnary (w.k + 1)) (zpuNatToUnary_unary (w.k + 1))).val
        (a.trunc (zpuNatToUnary (w.k + 1))
          (zpuNatToUnary_unary (w.k + 1))).val :=
    exactEq (zpuNatToUnary (w.k + 1)) (zpuNatToUnary_unary (w.k + 1))
  exact w.nz_succ (hsame_trans (hsame_symm transport) scaledZero)

def qpInvApart {p : BHist} (x : QpInt p) (hx : QpApart0 x) : QpInt p :=
  let w := firstNonzero hx.num_apart
  let u := zpDivPowExact x.value w.k w.zero_k
  let ui := ZpUnitInv u (divPowExact_unit w)
  { shift := w.k
    value := zpMul p (zpPowP p x.value.prime x.shift) ui }

theorem qpInvApart_value_identity {p : BHist} (x : QpInt p) (hx : QpApart0 x)
    (prime : NatPrime p) :
    ZpEq
      (zpMul p x.value (qpInvApart x hx).value)
      (zpScale p prime (x.shift + (qpInvApart x hx).shift)
        (zpOne p x.value.prime)) := by
  let w := firstNonzero hx.num_apart
  let u := zpDivPowExact x.value w.k w.zero_k
  let ui := ZpUnitInv u (divPowExact_unit w)
  have xFactor :
      ZpEq x.value (zpMul p (zpPowP p x.value.prime w.k) u) :=
    ZpEq_symm (pow_mul_divPowExact x.value w.k w.zero_k)
  have replaceX :
      ZpEq (zpMul p x.value (qpInvApart x hx).value)
        (zpMul p (zpMul p (zpPowP p x.value.prime w.k) u)
          (qpInvApart x hx).value) :=
    zpMul_left_congr xFactor
  have unfoldInv :
      ZpEq
        (zpMul p (zpMul p (zpPowP p x.value.prime w.k) u)
          (qpInvApart x hx).value)
        (zpMul p (zpMul p (zpPowP p x.value.prime w.k) u)
          (zpMul p (zpPowP p x.value.prime x.shift) ui)) := by
    unfold qpInvApart
    dsimp
    exact ZpEq_refl _
  have shuffle :
      ZpEq
        (zpMul p (zpMul p (zpPowP p x.value.prime w.k) u)
          (zpMul p (zpPowP p x.value.prime x.shift) ui))
        (zpMul p
          (zpMul p (zpPowP p x.value.prime w.k)
            (zpPowP p x.value.prime x.shift))
          (zpMul p u ui)) :=
    zpMul_pair_shuffle p (zpPowP p x.value.prime w.k) u
      (zpPowP p x.value.prime x.shift) ui
  have unitInv : ZpEq (zpMul p u ui) (zpOne p u.prime) :=
    ZpUnitInv_mul u (divPowExact_unit w)
  have replaceUnit :
      ZpEq
        (zpMul p
          (zpMul p (zpPowP p x.value.prime w.k)
            (zpPowP p x.value.prime x.shift))
          (zpMul p u ui))
        (zpMul p
          (zpMul p (zpPowP p x.value.prime w.k)
            (zpPowP p x.value.prime x.shift))
          (zpOne p u.prime)) :=
    zpMul_right_congr unitInv
  have powerAdd :
      ZpEq
        (zpMul p (zpPowP p x.value.prime w.k)
          (zpPowP p x.value.prime x.shift))
        (zpPowP p x.value.prime (w.k + x.shift)) :=
    pPowZp_mul_add p x.value.prime w.k x.shift
  have replacePower :
      ZpEq
        (zpMul p
          (zpMul p (zpPowP p x.value.prime w.k)
            (zpPowP p x.value.prime x.shift))
          (zpOne p u.prime))
        (zpMul p (zpPowP p x.value.prime (w.k + x.shift))
          (zpOne p u.prime)) :=
    zpMul_left_congr powerAdd
  have oneRight :
      ZpEq
        (zpMul p (zpPowP p x.value.prime (w.k + x.shift))
          (zpOne p u.prime))
        (zpPowP p x.value.prime (w.k + x.shift)) :=
    zpOne_mul_right p u.prime (zpPowP p x.value.prime (w.k + x.shift))
  have reindex :
      ZpEq
        (zpPowP p x.value.prime (w.k + x.shift))
        (zpPowP p prime (x.shift + w.k)) := by
    have primeSwitch :
        ZpEq
          (zpPowP p x.value.prime (w.k + x.shift))
          (zpPowP p prime (w.k + x.shift)) := by
      unfold zpPowP
      exact pPowZp_prime_irrel x.value.prime prime (w.k + x.shift)
    have sumSwitch :
        ZpEq
          (zpPowP p prime (w.k + x.shift))
          (zpPowP p prime (x.shift + w.k)) := by
      rw [Nat.add_comm w.k x.shift]
      exact ZpEq_refl _
    exact ZpEq_trans primeSwitch sumSwitch
  have toScale :
      ZpEq
        (zpPowP p prime (x.shift + w.k))
        (zpScale p prime (x.shift + w.k) (zpOne p x.value.prime)) :=
    ZpEq_symm (zpOne_mul_right p x.value.prime (zpPowP p prime (x.shift + w.k)))
  have targetUnfold :
      ZpEq
        (zpScale p prime (x.shift + w.k) (zpOne p x.value.prime))
        (zpScale p prime (x.shift + (qpInvApart x hx).shift)
          (zpOne p x.value.prime)) := by
    unfold qpInvApart
    dsimp
    exact ZpEq_refl _
  exact ZpEq_trans replaceX
    (ZpEq_trans unfoldInv
      (ZpEq_trans shuffle
        (ZpEq_trans replaceUnit
          (ZpEq_trans replacePower
            (ZpEq_trans oneRight
              (ZpEq_trans reindex
                (ZpEq_trans toScale targetUnfold)))))))

theorem qpInvApart_mul {p : BHist} (x : QpInt p) (hx : QpApart0 x) :
    QpEq (qpMul x (qpInvApart x hx)) (qpOne p x.value.prime) := by
  intro prime
  unfold QpRawEq QpCrossEq qpMul qpOne
  dsimp
  exact ZpEq_trans
    (zpOne_mul_left p prime
      (zpMul p x.value (qpInvApart x hx).value))
    (qpInvApart_value_identity x hx prime)

theorem qpInvApart_mul_right {p : BHist} (x : QpInt p) (hx : QpApart0 x) :
    QpEq (qpMul (qpInvApart x hx) x) (qpOne p x.value.prime) := by
  exact QpEq_trans (qpMul_comm (qpInvApart x hx) x)
    (qpInvApart_mul x hx)

structure QpFieldCore (p : BHist) extends QpApartLocalizationCore p where
  inv_apart : ∀ x : QpInt p, QpApart0 x -> QpInt p
  mul_inv_apart : ∀ (x : QpInt p) (hx : QpApart0 x),
    QpEq (qpMul x (inv_apart x hx)) (qpOne p x.value.prime)
  inv_apart_mul : ∀ (x : QpInt p) (hx : QpApart0 x),
    QpEq (qpMul (inv_apart x hx) x) (qpOne p x.value.prime)

def QpInt_field_core (p : BHist) : QpFieldCore p :=
  { QpInt_apart_localization_core p with
    inv_apart := qpInvApart
    mul_inv_apart := qpInvApart_mul
    inv_apart_mul := qpInvApart_mul_right }

end BEDC.Derived.PadicUp
