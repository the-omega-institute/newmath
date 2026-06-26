import BEDC.Derived.PadicUp.IntegerTower.RingCompletion
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

-- 这个文件承载模素数层的可计算逆元构造。

private theorem natOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

private theorem natModFn_one_of_prime {p : BHist} (prime : NatPrime p) :
    hsame (natModFn p NatOne) NatOne := by
  exact natModFn_of_strict prime.left (NatPrime_empty_absurd prime) natOne_unary
    prime.right.left

private theorem unit_strict_of_nonzero_nonunit {r : BHist} :
    UnaryHistory r -> (hsame r BHist.Empty -> False) ->
      (r = NatOne -> False) -> NatUnaryStrictPrefix NatOne r := by
  intro rUnary rNonzero rNonunit
  have total := NatUnaryPrefix_trichotomy_hsame_strict natOne_unary rUnary
  cases total with
  | inl same =>
      exact False.elim (rNonunit (hsame_symm same))
  | inr rest =>
      cases rest with
      | inl unitLt =>
          exact unitLt
      | inr rLtUnit =>
          have boundary := NatUnaryStrictPrefix_successor_boundary_local rUnary rLtUnit
          cases boundary with
          | inl rEmpty =>
              exact False.elim (rNonzero rEmpty)
          | inr rLtEmpty =>
              exact False.elim (NatUnaryStrictPrefix_empty_right_absurd rLtEmpty)

private theorem natModFn_complement_add_raw_right_zero {M r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory r ->
      hsame
        (natModFn M (append (natComplementMod M r) r))
        BHist.Empty := by
  intro MUnary MNonempty rUnary
  have compUnary : UnaryHistory (natComplementMod M r) :=
    natComplementMod_unary MUnary
  have remUnary : UnaryHistory (natModFn M r) :=
    natModFn_unary MUnary rUnary MNonempty
  have raw :
      hsame
        (natModFn M (append (natComplementMod M r) (natModFn M r)))
        BHist.Empty :=
    natComplementMod_add_right_zero MUnary MNonempty rUnary
  have replaceTail :
      hsame
        (natModFn M (append (natComplementMod M r) (natModFn M r)))
        (natModFn M (append (natComplementMod M r) r)) :=
    natModFn_add_congruence MUnary MNonempty compUnary remUnary compUnary rUnary
      (hsame_refl _)
      (mod_idem MUnary MNonempty rUnary)
  exact hsame_trans (hsame_symm replaceTail) raw

private theorem natModFn_mul_sum_zero {M a b c : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
        hsame (natModFn M (append b c)) BHist.Empty ->
          hsame
            (natModFn M (append (natMulFn a b) (natMulFn a c)))
            BHist.Empty := by
  intro MUnary MNonempty aUnary bUnary cUnary sumZero
  have bcUnary : UnaryHistory (append b c) := unary_append_closed bUnary cUnary
  have remBCUnary : UnaryHistory (natModFn M (append b c)) :=
    natModFn_unary MUnary bcUnary MNonempty
  have productReduced :
      hsame
        (natModFn M (natMulFn a (natModFn M (append b c))))
        (natModFn M (natMulFn a (append b c))) :=
    natModFn_mul_right_reduce_same_mod MUnary MNonempty aUnary bcUnary
  have productZero :
      hsame
        (natModFn M (natMulFn a (natModFn M (append b c))))
        BHist.Empty := by
    have productSame :
        hsame
          (natModFn M (natMulFn a (natModFn M (append b c))))
          (natModFn M (natMulFn a BHist.Empty)) :=
      natModFn_hsame_arg_transport (M := M)
        (natMulFn_hsame_transport (hsame_refl a) sumZero)
    exact productSame
  have rawZero :
      hsame (natModFn M (natMulFn a (append b c))) BHist.Empty :=
    hsame_trans (hsame_symm productReduced) productZero
  have distrib :
      hsame
        (natModFn M (natMulFn a (append b c)))
        (natModFn M (append (natMulFn a b) (natMulFn a c))) :=
    natModFn_mul_add_distrib MUnary MNonempty aUnary bUnary cUnary
  exact hsame_trans (hsame_symm distrib) rawZero

private theorem natModFn_mul_complement_add_right_zero {M a t : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory t ->
        hsame
          (natModFn M
            (append
              (natMulFn a (natComplementMod M t))
              (natMulFn a t)))
          BHist.Empty := by
  intro MUnary MNonempty aUnary tUnary
  exact natModFn_mul_sum_zero MUnary MNonempty aUnary
    (natComplementMod_unary MUnary) tUnary
    (natModFn_complement_add_raw_right_zero MUnary MNonempty tUnary)

private theorem natMulFn_assoc_hsame {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn a (natMulFn b c)) (natMulFn (natMulFn a b) c) := by
  intro aUnary bUnary cUnary
  have abUnary : UnaryHistory (natMulFn a b) := natMulFn_unary aUnary bUnary
  have bcUnary : UnaryHistory (natMulFn b c) := natMulFn_unary bUnary cUnary
  exact hsame_symm
    (NatMul_assoc_hsame aUnary bUnary cUnary
      (natMulFn_rel aUnary bUnary)
      (natMulFn_rel abUnary cUnary)
      (natMulFn_rel bUnary cUnary)
      (natMulFn_rel aUnary bcUnary))

private theorem natMulFn_commute_left_pair {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn a (natMulFn b c)) (natMulFn b (natMulFn a c)) := by
  intro aUnary bUnary cUnary
  have acUnary : UnaryHistory (natMulFn a c) := natMulFn_unary aUnary cUnary
  have bcUnary : UnaryHistory (natMulFn b c) := natMulFn_unary bUnary cUnary
  have abUnary : UnaryHistory (natMulFn a b) := natMulFn_unary aUnary bUnary
  have baUnary : UnaryHistory (natMulFn b a) := natMulFn_unary bUnary aUnary
  have leftAssoc :
      hsame (natMulFn a (natMulFn b c)) (natMulFn (natMulFn a b) c) :=
    natMulFn_assoc_hsame aUnary bUnary cUnary
  have middle :
      hsame (natMulFn (natMulFn a b) c) (natMulFn (natMulFn b a) c) :=
    natMulFn_hsame_transport
      (natMulFn_comm_hsame aUnary bUnary) (hsame_refl c)
  have rightAssoc :
      hsame (natMulFn (natMulFn b a) c) (natMulFn b (natMulFn a c)) :=
    hsame_symm (natMulFn_assoc_hsame bUnary aUnary cUnary)
  exact hsame_trans leftAssoc (hsame_trans middle rightAssoc)

private theorem natModFn_divrem_inverse_step {p r invS : BHist} :
    NatPrime p -> UnaryHistory r -> (hsame r BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne r -> NatDivRem r p (natQuotFn r p) (natModFn r p) ->
        UnaryHistory invS ->
          hsame (natModFn p (natMulFn (natModFn r p) invS)) (natModFn p NatOne) ->
            hsame
              (natModFn p
                (natMulFn r
                  (natComplementMod p
                    (append
                      (natMulFn (natQuotFn r p) invS)
                      BHist.Empty))))
              (natModFn p NatOne) := by
  intro prime rUnary rNonzero unitLtR divrem invSUnary sInv
  let q := natQuotFn r p
  let s := natModFn r p
  let sInvRaw := natMulFn s invS
  let qInv := natMulFn q invS
  let t := append qInv BHist.Empty
  let c := natComplementMod p t
  let rT := natMulFn r t
  have pNonempty : hsame p BHist.Empty -> False := NatPrime_empty_absurd prime
  have qUnary : UnaryHistory q := NatDivRem_quotient_unary divrem
  have sUnary : UnaryHistory s := NatDivRem_remainder_unary divrem
  have qInvUnary : UnaryHistory qInv := natMulFn_unary qUnary invSUnary
  have sInvRawUnary : UnaryHistory sInvRaw := natMulFn_unary sUnary invSUnary
  have tUnary : UnaryHistory t := unary_append_closed qInvUnary unary_empty
  have cUnary : UnaryHistory c := natComplementMod_unary prime.left
  have rTUnary : UnaryHistory rT := natMulFn_unary rUnary tUnary
  have rCUnary : UnaryHistory (natMulFn r c) := natMulFn_unary rUnary cUnary
  have tSameQInv : hsame t qInv := append_empty_right qInv
  have rTSameRQInv : hsame rT (natMulFn r qInv) :=
    natMulFn_hsame_transport (hsame_refl r) tSameQInv
  cases divrem with
  | intro rq rqData =>
          have rqUnary : UnaryHistory rq := NatMul_result_unary rUnary rqData.left
          have rqInvUnary : UnaryHistory (natMulFn rq invS) :=
            natMulFn_unary rqUnary invSUnary
          have addProducts : NatAdd (natMulFn rq invS) sInvRaw (natMulFn p invS) :=
            NatMul_add_right_distrib rqData.right.left
              (natMulFn_rel prime.left invSUnary)
              (natMulFn_rel rqUnary invSUnary)
              (natMulFn_rel sUnary invSUnary)
          have pDividesPInv : NatDivides p (natMulFn p invS) :=
            ⟨invS, invSUnary, natMulFn_rel prime.left invSUnary⟩
          have pDividesRqS :
              NatDivides p (append (natMulFn rq invS) sInvRaw) := by
            have sumSame : hsame (natMulFn p invS)
                (append (natMulFn rq invS) sInvRaw) :=
              addProducts.right.right
            exact (NatDivides_dividend_hsame_transport pDividesPInv sumSame).right
          have rqSZero :
              hsame
                (natModFn p (append (natMulFn rq invS) sInvRaw))
                BHist.Empty :=
            (dvd_iff_mod_zero prime.left pNonempty
              (unary_append_closed rqInvUnary sInvRawUnary)).mp pDividesRqS
          have rqOneCongr :
              hsame
                (natModFn p (append (natMulFn rq invS) sInvRaw))
                (natModFn p (append (natMulFn rq invS) NatOne)) :=
            natModFn_add_congruence prime.left pNonempty
              rqInvUnary sInvRawUnary rqInvUnary natOne_unary
              (hsame_refl _) sInv
          have rqOneZero :
              hsame
                (natModFn p (append (natMulFn rq invS) NatOne))
                BHist.Empty :=
            hsame_trans (hsame_symm rqOneCongr) rqSZero
          have pDividesRqOne :
              NatDivides p (append (natMulFn rq invS) NatOne) :=
            (dvd_iff_mod_zero prime.left pNonempty
              (unary_append_closed rqInvUnary natOne_unary)).mpr rqOneZero
          have rqSame : hsame rq (natMulFn r q) :=
            NatMul_functional rUnary rqData.left (natMulFn_rel rUnary qUnary)
          have rqInvSameRTerm :
              hsame (natMulFn rq invS) (natMulFn r qInv) := by
            have rqTransport :
                hsame (natMulFn rq invS) (natMulFn (natMulFn r q) invS) :=
              natMulFn_hsame_transport rqSame (hsame_refl invS)
            have assoc :
                hsame (natMulFn r qInv) (natMulFn (natMulFn r q) invS) :=
              natMulFn_assoc_hsame rUnary qUnary invSUnary
            exact hsame_trans rqTransport (hsame_symm assoc)
          have rTermUnary : UnaryHistory (natMulFn r qInv) :=
            natMulFn_unary rUnary qInvUnary
          have pDividesRTOne : NatDivides p (append rT NatOne) := by
            have sameRqOneRTOne :
                hsame (append (natMulFn rq invS) NatOne) (append rT NatOne) :=
              cont_respects_hsame
                (hsame_trans rqInvSameRTerm (hsame_symm rTSameRQInv))
                (hsame_refl NatOne)
                (cont_intro rfl) (cont_intro rfl)
            exact (NatDivides_dividend_hsame_transport pDividesRqOne sameRqOneRTOne).right
          have pDividesOneRT : NatDivides p (append NatOne rT) := by
            have sameOrder : hsame (append rT NatOne) (append NatOne rT) :=
              unary_append_comm rTUnary natOne_unary
            exact (NatDivides_dividend_hsame_transport pDividesRTOne sameOrder).right
          have oneRTZero :
              hsame (natModFn p (append NatOne rT)) BHist.Empty :=
            (dvd_iff_mod_zero prime.left pNonempty
              (unary_append_closed natOne_unary rTUnary)).mp pDividesOneRT
          have compRawZero :
              hsame (natModFn p (append (natMulFn r c) rT)) BHist.Empty :=
            natModFn_mul_complement_add_right_zero prime.left pNonempty rUnary tUnary
          have remRCUnary : UnaryHistory (natModFn p (natMulFn r c)) :=
            natModFn_unary prime.left rCUnary pNonempty
          have reduceComp :
              hsame
                (natModFn p (append (natMulFn r c) rT))
                (natModFn p (append (natModFn p (natMulFn r c)) rT)) :=
            natModFn_add_congruence prime.left pNonempty
              rCUnary rTUnary remRCUnary rTUnary
              (hsame_symm (mod_idem prime.left pNonempty rCUnary))
              (hsame_refl _)
          have remCompZero :
              hsame
                (natModFn p (append (natModFn p (natMulFn r c)) rT))
                BHist.Empty :=
            hsame_trans (hsame_symm reduceComp) compRawZero
          have remCompStrict : NatUnaryStrictPrefix (natModFn p (natMulFn r c)) p :=
            natModFn_lt prime.left rCUnary pNonempty
          have remCompSameOne :
              hsame (natModFn p (natMulFn r c)) NatOne :=
            natModFn_add_inverse_unique prime.left pNonempty rTUnary
              remRCUnary natOne_unary remCompStrict prime.right.left
              remCompZero oneRTZero
          exact hsame_trans remCompSameOne
            (hsame_symm (natModFn_one_of_prime prime))

private structure InvModPrimeCandidate where
  val : BHist
  unary : UnaryHistory val

private def invModPrimeCorePack (p r : BHist) (pUnary : UnaryHistory p) :
    Nat -> InvModPrimeCandidate
  | 0 => { val := NatOne, unary := natOne_unary }
  | fuel + 1 =>
      if _unit : r = NatOne then
        { val := NatOne, unary := natOne_unary }
      else
        let s := natModFn r p
        if _zero : s = BHist.Empty then
          { val := NatOne, unary := natOne_unary }
        else
          { val :=
              natComplementMod p
                (append
                  (natMulFn (natQuotFn r p) (invModPrimeCorePack p s pUnary fuel).val)
                  BHist.Empty),
            unary := natComplementMod_unary pUnary }

private def invModPrimeCore (p r : BHist) (pUnary : UnaryHistory p) (fuel : Nat) :
    BHist :=
  (invModPrimeCorePack p r pUnary fuel).val

private theorem invModPrimeCore_unary {p r : BHist} (pUnary : UnaryHistory p)
    (fuel : Nat) :
    UnaryHistory (invModPrimeCore p r pUnary fuel) :=
  (invModPrimeCorePack p r pUnary fuel).unary

set_option maxHeartbeats 800000 in
private theorem invModPrimeCore_spec {p r : BHist} (prime : NatPrime p)
    (rUnary : UnaryHistory r) (rNonzero : hsame r BHist.Empty -> False)
    (rLtP : NatUnaryStrictPrefix r p) :
    ∀ fuel : Nat,
      BEDC.FKernel.ExternalBinary.bwordLength r < fuel ->
        hsame
          (natModFn p
        (natMulFn r (invModPrimeCore p r prime.left fuel)))
          (natModFn p NatOne) := by
  intro fuel
  induction fuel generalizing r with
  | zero =>
      intro lengthLt
      exact False.elim (Nat.not_lt_zero _ lengthLt)
  | succ fuel ih =>
      intro lengthLt
      unfold invModPrimeCore invModPrimeCorePack
      by_cases unit : r = NatOne
      · rw [dif_pos unit]
        cases unit
        have unitProduct :
            hsame (natMulFn NatOne NatOne) NatOne :=
          NatMul_unit_left_hsame natOne_unary
            (natMulFn_rel natOne_unary natOne_unary)
        exact hsame_trans
          (natModFn_hsame_arg_transport (M := p) unitProduct)
          (hsame_refl _)
      · rw [dif_neg unit]
        let s := natModFn r p
        by_cases zero : s = BHist.Empty
        · rw [dif_pos zero]
          have divrem : NatDivRem r p (natQuotFn r p) s :=
            natModFn_spec rUnary prime.left rNonzero
          have dvdRP : NatDivides r p :=
            (dvd_iff_rem_zero rUnary rNonzero divrem).mpr zero
          have unitLtR : NatUnaryStrictPrefix NatOne r :=
            unit_strict_of_nonzero_nonunit rUnary rNonzero unit
          exact False.elim (prime_no_proper_divisor prime rUnary unitLtR rLtP dvdRP)
        · rw [dif_neg zero]
          have sUnary : UnaryHistory s :=
            natModFn_unary rUnary prime.left rNonzero
          have sLtR : NatUnaryStrictPrefix s r :=
            natModFn_lt rUnary prime.left rNonzero
          have sNonzero : hsame s BHist.Empty -> False := by
            intro sEmpty
            exact zero sEmpty
          have sLtP : NatUnaryStrictPrefix s p :=
            NatUnaryStrictPrefix_trans sLtR rLtP
          have lengthSLtR :
              BEDC.FKernel.ExternalBinary.bwordLength s <
                BEDC.FKernel.ExternalBinary.bwordLength r :=
            NatUnaryStrictPrefix_length_lt sUnary sLtR
          have lengthSLtFuel :
              BEDC.FKernel.ExternalBinary.bwordLength s < fuel := by
            exact Nat.lt_of_lt_of_le lengthSLtR (Nat.le_of_lt_succ lengthLt)
          have recSpec :=
            ih sUnary sNonzero sLtP lengthSLtFuel
          have divrem : NatDivRem r p (natQuotFn r p) s :=
            natModFn_spec rUnary prime.left rNonzero
          exact natModFn_divrem_inverse_step prime rUnary rNonzero
            (unit_strict_of_nonzero_nonunit rUnary rNonzero unit)
            divrem
            (invModPrimeCore_unary prime.left fuel)
            recSpec

private def invModPrimeRaw (p r : BHist) (pUnary : UnaryHistory p) : BHist :=
  invModPrimeCore p r pUnary (BEDC.FKernel.ExternalBinary.bwordLength r + 1)

private theorem invModPrimeRaw_unary {p r : BHist} (pUnary : UnaryHistory p) :
    UnaryHistory (invModPrimeRaw p r pUnary) := by
  unfold invModPrimeRaw
  exact invModPrimeCore_unary pUnary _

private theorem invModPrimeRaw_spec {p : BHist} (prime : NatPrime p) (r : BoundedNat p)
    (rNonzero : hsame r.val BHist.Empty -> False) :
      hsame
        (natModFn p (natMulFn r.val (invModPrimeRaw p r.val prime.left)))
        (natModFn p NatOne) := by
  unfold invModPrimeRaw
  have rUnary : UnaryHistory r.val := BoundedNat_unary prime.left r
  have lengthLt :
      BEDC.FKernel.ExternalBinary.bwordLength r.val <
      BEDC.FKernel.ExternalBinary.bwordLength r.val + 1 :=
    Nat.lt_succ_self _
  exact invModPrimeCore_spec prime rUnary rNonzero r.isLt
    (BEDC.FKernel.ExternalBinary.bwordLength r.val + 1) lengthLt

def invModPrime {p : BHist} (prime : NatPrime p) (r : BoundedNat p)
    (_rNonzero : hsame r.val BHist.Empty -> False) : BoundedNat p :=
  { val := natModFn p (invModPrimeRaw p r.val prime.left)
    isLt := natModFn_strict_all prime.left (NatPrime_empty_absurd prime) }

theorem invModPrime_spec {p : BHist} (prime : NatPrime p) (r : BoundedNat p)
    (rNonzero : hsame r.val BHist.Empty -> False) :
      hsame
        (natModFn p
          (natMulFn r.val (invModPrime prime r rNonzero).val))
        (natModFn p NatOne) := by
  unfold invModPrime
  have pNonempty : hsame p BHist.Empty -> False := NatPrime_empty_absurd prime
  have rUnary : UnaryHistory r.val := BoundedNat_unary prime.left r
  have rawUnary : UnaryHistory (invModPrimeRaw p r.val prime.left) :=
    invModPrimeRaw_unary prime.left
  have reduceRight :
      hsame
        (natModFn p (natMulFn r.val (natModFn p (invModPrimeRaw p r.val prime.left))))
        (natModFn p (natMulFn r.val (invModPrimeRaw p r.val prime.left))) :=
    natModFn_mul_right_reduce_same_mod prime.left pNonempty rUnary rawUnary
  exact hsame_trans reduceRight (invModPrimeRaw_spec prime r rNonzero)

end BEDC.Derived.PadicUp
