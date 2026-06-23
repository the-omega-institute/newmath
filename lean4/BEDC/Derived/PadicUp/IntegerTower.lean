import BEDC.Derived.PadicUp.Multiplicative
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def zpuNatToUnary : Nat -> BHist :=
  BEDC.Derived.IntUp.natToUnary

theorem zpuNatToUnary_unary (n : Nat) : UnaryHistory (zpuNatToUnary n) :=
  BEDC.Derived.IntUp.natToUnary_unary n

theorem zpuNatToUnary_length (n : Nat) : bwordLength (zpuNatToUnary n) = n :=
  BEDC.Derived.IntUp.natToUnary_length n

theorem zpu_hsame_of_unary_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

theorem zpu_natToUnary_hsame_of_length {h : BHist} :
    UnaryHistory h -> hsame (zpuNatToUnary (bwordLength h)) h := by
  intro hUnary
  exact zpu_hsame_of_unary_length (zpuNatToUnary_unary _) hUnary
    (zpuNatToUnary_length _)

theorem NatUnaryStrictPrefix_of_length_lt {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h < bwordLength k ->
      NatUnaryStrictPrefix h k := by
  intro hUnary kUnary lengthLt
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl left =>
      cases left with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp same
              exact False.elim (Nat.lt_irrefl _ (lengthEq ▸ lengthLt))
          | inr strict =>
              exact strict
  | inr right =>
      cases right with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp
                  (hsame_symm same)
              exact False.elim (Nat.lt_irrefl _ (lengthEq ▸ lengthLt))
          | inr strictKH =>
              have kLtH := NatUnaryStrictPrefix_length_lt kUnary strictKH
              exact False.elim (Nat.lt_asymm lengthLt kLtH)

theorem zpuNatToUnary_NatMul_rel (a b : Nat) :
    NatMul (zpuNatToUnary a) (zpuNatToUnary b) (zpuNatToUnary (a * b)) := by
  have leftUnary := zpuNatToUnary_unary a
  have rightUnary := zpuNatToUnary_unary b
  have total := NatMul_total leftUnary rightUnary
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (zpuNatToUnary (a * b)) :=
        zpu_hsame_of_unary_length resultData.left (zpuNatToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans
            (by rw [zpuNatToUnary_length, zpuNatToUnary_length, zpuNatToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

def pPowCanon (p N : BHist) : BHist :=
  zpuNatToUnary (bwordLength p ^ bwordLength N)

theorem pPowCanon_unary (p N : BHist) : UnaryHistory (pPowCanon p N) :=
  zpuNatToUnary_unary _

theorem pPowCanon_length (p N : BHist) :
    bwordLength (pPowCanon p N) = bwordLength p ^ bwordLength N :=
  zpuNatToUnary_length _

theorem pPowCanon_PPow {p N : BHist} :
    UnaryHistory p -> UnaryHistory N -> PPow p N (pPowCanon p N) := by
  intro pUnary NUnary
  induction N with
  | Empty =>
      change PPow p BHist.Empty (zpuNatToUnary (bwordLength p ^ 0))
      have sameOne : hsame (zpuNatToUnary (bwordLength p ^ 0)) NatOne :=
        zpu_hsame_of_unary_length (zpuNatToUnary_unary _) (unary_e1_closed unary_empty)
          (by rw [zpuNatToUnary_length]; rfl)
      exact PPow_result_hsame_transport (PPow.zero pUnary) (hsame_symm sameOne)
  | e0 _ _ =>
      cases NUnary
  | e1 tail ih =>
      have tailUnary : UnaryHistory tail := unary_e1_inversion NUnary
      have prevPow := ih tailUnary
      have raw :
          NatMul (zpuNatToUnary (bwordLength p))
            (zpuNatToUnary (bwordLength p ^ bwordLength tail))
            (zpuNatToUnary (bwordLength p * bwordLength p ^ bwordLength tail)) :=
        zpuNatToUnary_NatMul_rel _ _
      have sameP : hsame (zpuNatToUnary (bwordLength p)) p :=
        zpu_natToUnary_hsame_of_length pUnary
      have sameResult :
          hsame (zpuNatToUnary (bwordLength p * bwordLength p ^ bwordLength tail))
            (pPowCanon p (BHist.e1 tail)) :=
        zpu_hsame_of_unary_length (zpuNatToUnary_unary _) (pPowCanon_unary p (BHist.e1 tail))
          (by
            rw [zpuNatToUnary_length, pPowCanon_length]
            rw [NatUp_unary_standard_bridge.right.left tail tailUnary]
            rw [Nat.pow_succ]
            exact Nat.mul_comm _ _)
      have step :
          NatMul p (pPowCanon p tail) (pPowCanon p (BHist.e1 tail)) :=
        (NatMul_operation_congruence raw sameP (hsame_refl _) sameResult).left
      exact PPow.succ prevPow step

theorem pPowCanon_nonempty_of_prime {p N : BHist} :
    NatPrime p -> UnaryHistory N -> hsame (pPowCanon p N) BHist.Empty -> False := by
  intro prime NUnary emptyPower
  exact PPow_nonempty_result (NatPrime_empty_absurd prime)
    (pPowCanon_PPow prime.left NUnary) emptyPower

theorem pPowCanon_positive_of_prime {p N : BHist} :
    NatPrime p -> UnaryHistory N -> 0 < bwordLength (pPowCanon p N) := by
  intro prime NUnary
  cases Nat.eq_zero_or_pos (bwordLength (pPowCanon p N)) with
  | inl zeroLen =>
      have emptyPower : hsame (pPowCanon p N) BHist.Empty :=
        zpu_hsame_of_unary_length (pPowCanon_unary p N) unary_empty
          (zeroLen.trans (NatUp_unary_standard_bridge.left).symm)
      exact False.elim (pPowCanon_nonempty_of_prime prime NUnary emptyPower)
  | inr positive =>
      exact positive

def NatUnaryPrefix (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ Cont h tail k

theorem pow_dvd_pow_of_le {p N K : BHist}
    (prime : NatPrime p) (NUnary : UnaryHistory N) (_KUnary : UnaryHistory K)
    (pref : NatUnaryPrefix N K) :
      NatDivides (pPowCanon p N) (pPowCanon p K) := by
  cases pref with
  | intro tail tailData =>
      have tailUnary : UnaryHistory tail := tailData.left
      have KAdd : NatAdd N tail K := ⟨NUnary, tailUnary, tailData.right⟩
      have powN := pPowCanon_PPow prime.left NUnary
      have powTail := pPowCanon_PPow prime.left tailUnary
      have pNUnary := pPowCanon_unary p N
      have pTailUnary := pPowCanon_unary p tail
      have productTotal := NatMul_total pNUnary pTailUnary
      cases productTotal with
      | intro product productData =>
          have powKProduct : PPow p K product :=
            PPow_add powN powTail KAdd productData.right
          have powKCanon := pPowCanon_PPow prime.left
            (NatAdd_result_unary KAdd)
          have sameProduct : hsame product (pPowCanon p K) :=
            PPow_functional powKProduct powKCanon
          exact ⟨pPowCanon p tail, pTailUnary,
            (NatMul_result_hsame_transport productData.right sameProduct).right⟩

theorem rem_rem_of_dvd {M K n qK rK qM rM qNested rNested : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      NatDivides M K ->
      NatDivRem K n qK rK ->
        NatDivRem M n qM rM ->
          NatDivRem M rK qNested rNested ->
            hsame rNested rM := by
  intro MUnary MNonempty dividesMK divremK divremM divremNested
  cases divremK with
  | intro kq kData =>
      have dividesKQ : NatDivides M kq := by
        exact NatDivides_mul_right_factor_closed (NatDivRem_quotient_unary ⟨kq, kData⟩)
          dividesMK kData.left
      cases divremNested with
      | intro nestedProduct nestedData =>
          have dividesNestedProductByM : NatDivides M nestedProduct :=
            ⟨qNested, NatMul_right_unary nestedData.left, nestedData.left⟩
          have displayedNested :
              Cont (BEDC.FKernel.Cont.append kq nestedProduct) rNested n := by
            exact cont_intro
              (by
                calc
                  n = BEDC.FKernel.Cont.append kq rK := kData.right.left.right.right
                  _ = BEDC.FKernel.Cont.append kq
                        (BEDC.FKernel.Cont.append nestedProduct rNested) :=
                    congrArg (fun h => BEDC.FKernel.Cont.append kq h)
                      nestedData.right.left.right.right
                  _ = BEDC.FKernel.Cont.append
                        (BEDC.FKernel.Cont.append kq nestedProduct) rNested :=
                    (BEDC.FKernel.Cont.append_assoc kq nestedProduct rNested).symm)
          have dividesDisplayedProduct : NatDivides M (BEDC.FKernel.Cont.append kq nestedProduct) :=
            NatDivides_cont_closed dividesKQ dividesNestedProductByM (cont_intro rfl)
          cases dividesDisplayedProduct with
          | intro displayedQuotient displayedQuotientData =>
              have displayedDirect :
                  NatAdd (BEDC.FKernel.Cont.append kq nestedProduct) rNested n :=
                ⟨NatMul_result_unary MUnary displayedQuotientData.right,
                  NatAdd_right_unary nestedData.right.left,
                  displayedNested⟩
              have synthetic : NatDivRem M n displayedQuotient rNested :=
                ⟨BEDC.FKernel.Cont.append kq nestedProduct, displayedQuotientData.right,
                  displayedDirect, nestedData.right.right⟩
              exact (divRem_unique MUnary MNonempty synthetic divremM).right

def natMod (M n : BHist) : BHist :=
  zpuNatToUnary (bwordLength n % bwordLength M)

theorem natMod_unary (M n : BHist) : UnaryHistory (natMod M n) :=
  zpuNatToUnary_unary _

theorem natMod_length (M n : BHist) :
    bwordLength (natMod M n) = bwordLength n % bwordLength M :=
  zpuNatToUnary_length _

theorem natMod_strict {M n : BHist} :
    UnaryHistory M -> 0 < bwordLength M -> NatUnaryStrictPrefix (natMod M n) M := by
  intro MUnary MPositive
  exact NatUnaryStrictPrefix_of_length_lt (natMod_unary M n) MUnary
    (by
      rw [natMod_length]
      exact Nat.mod_lt _ MPositive)

structure BoundedNat (M : BHist) where
  val : BHist
  isLt : NatUnaryStrictPrefix val M

def ZpTrunc (p N : BHist) : Type :=
  BoundedNat (pPowCanon p N)

def fromNatModPow (p N n : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N) :
    ZpTrunc p N :=
  { val := natMod (pPowCanon p N) n
    isLt := natMod_strict (pPowCanon_unary p N)
      (pPowCanon_positive_of_prime prime NUnary) }

def ZpEqTrunc {p N : BHist} (x y : ZpTrunc p N) : Prop :=
  hsame x.val y.val

def reduce (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x : ZpTrunc p (BHist.e1 N)) : ZpTrunc p N :=
  fromNatModPow p N x.val prime NUnary

def ZpCompatible (p : BHist) (prime : NatPrime p)
    (trunc : (N : BHist) -> UnaryHistory N -> ZpTrunc p N) : Prop :=
  ∀ (N : BHist) (NUnary : UnaryHistory N),
    ZpEqTrunc (reduce p N prime NUnary
      (trunc (BHist.e1 N) (unary_e1_closed NUnary))) (trunc N NUnary)

structure ZpInt (p : BHist) where
  prime : NatPrime p
  trunc : (N : BHist) -> UnaryHistory N -> ZpTrunc p N
  compat : ZpCompatible p prime trunc

def ZpEq {p : BHist} (x y : ZpInt p) : Prop :=
  ∀ (N : BHist) (NUnary : UnaryHistory N),
    hsame (x.trunc N NUnary).val (y.trunc N NUnary).val

def fromIntModPow (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x : BHist × BHist) : ZpTrunc p N :=
  fromNatModPow p N (BEDC.FKernel.Cont.append x.1 (natMod (pPowCanon p N) x.2))
    prime NUnary

def intPairToZp (p : BHist) (prime : NatPrime p) (x : BHist × BHist)
    (compat :
      ZpCompatible p prime (fun N NUnary => fromIntModPow p N prime NUnary x)) : ZpInt p :=
  { prime := prime
    trunc := fun N NUnary => fromIntModPow p N prime NUnary x
    compat := compat }

def zpZero (p : BHist) (prime : NatPrime p)
    (compat :
      ZpCompatible p prime
        (fun N NUnary => fromIntModPow p N prime NUnary (BHist.Empty, BHist.Empty))) :
    ZpInt p :=
  intPairToZp p prime (BHist.Empty, BHist.Empty) compat

def zpOne (p : BHist) (prime : NatPrime p)
    (compat :
      ZpCompatible p prime
        (fun N NUnary => fromIntModPow p N prime NUnary (NatOne, BHist.Empty))) :
    ZpInt p :=
  intPairToZp p prime (NatOne, BHist.Empty) compat

def zpAddTrunc (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x y : ZpTrunc p N) : ZpTrunc p N :=
  fromNatModPow p N (BEDC.FKernel.Cont.append x.val y.val) prime NUnary

def zpAdd (p : BHist) (x y : ZpInt p)
    (compat :
      ZpCompatible p x.prime
        (fun N NUnary => zpAddTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary))) :
    ZpInt p :=
  { prime := x.prime
    trunc := fun N NUnary => zpAddTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary)
    compat := compat }

def natDistanceInt (x y : BHist) : BMark × BHist :=
  if bwordLength y ≤ bwordLength x then
    (BMark.b0, zpuNatToUnary (bwordLength x - bwordLength y))
  else
    (BMark.b1, zpuNatToUnary (bwordLength y - bwordLength x))

theorem natDistanceInt_carrier (x y : BHist) :
    IntCarrier (natDistanceInt x y).1 (natDistanceInt x y).2 := by
  unfold natDistanceInt
  split
  · exact ⟨Or.inl rfl, zpuNatToUnary_unary _⟩
  · exact ⟨Or.inr rfl, zpuNatToUnary_unary _⟩

def Ball (p N x y : BHist) : Prop :=
  PDvdInt p N (natDistanceInt x y)

theorem Ball_carrier {p N x y : BHist} :
    Ball p N x y -> IntCarrier (natDistanceInt x y).1 (natDistanceInt x y).2 := by
  intro ball
  exact ball.left

end BEDC.Derived.PadicUp
