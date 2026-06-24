import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.Order
import BEDC.Derived.IntUp.ZeroRepresentative
import BEDC.Derived.NatUp
import BEDC.Derived.PadicUp.Multiplicative
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp

structure RatNum where
  num : IntegerUp
  den : BHist
  den_pos : NatUnaryStrictPrefix NatOne den ∨ hsame den NatOne

def ratDenCarrier (x : RatNum) : UnaryHistory x.den := by
  cases x.den_pos with
  | inl strict =>
      cases strict with
      | intro tail data =>
          exact unary_cont_closed (unary_e1_closed unary_empty) data.left data.right.right
  | inr same =>
      exact unary_transport (unary_e1_closed unary_empty) (hsame_symm same)

theorem ratDen_nonempty (x : RatNum) : hsame x.den BHist.Empty -> False := by
  intro empty
  cases x.den_pos with
  | inl strict =>
      have oneLt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
      have denZero :
          BEDC.FKernel.ExternalBinary.bwordLength x.den = 0 := by
        have emptyLen := congrArg BEDC.FKernel.ExternalBinary.bwordLength empty
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at emptyLen
        exact emptyLen
      rw [denZero] at oneLt
      cases oneLt
  | inr same =>
      exact not_hsame_e1_empty (hsame_trans (hsame_symm same) empty)

def ratDenPosMul {a b : BHist}
    (ha : NatUnaryStrictPrefix NatOne a ∨ hsame a NatOne)
    (hb : NatUnaryStrictPrefix NatOne b ∨ hsame b NatOne) :
    NatUnaryStrictPrefix NatOne (natMulFn a b) ∨
      hsame (natMulFn a b) NatOne := by
  have aUnary : UnaryHistory a := by
    cases ha with
    | inl strict =>
        cases strict with
        | intro tail data =>
            exact unary_cont_closed (unary_e1_closed unary_empty) data.left data.right.right
    | inr same => exact unary_transport (unary_e1_closed unary_empty) (hsame_symm same)
  have bUnary : UnaryHistory b := by
    cases hb with
    | inl strict =>
        cases strict with
        | intro tail data =>
            exact unary_cont_closed (unary_e1_closed unary_empty) data.left data.right.right
    | inr same => exact unary_transport (unary_e1_closed unary_empty) (hsame_symm same)
  have productUnary : UnaryHistory (natMulFn a b) := natMulFn_unary aUnary bUnary
  have lengthA : 1 ≤ BEDC.FKernel.ExternalBinary.bwordLength a := by
    cases ha with
    | inl strict =>
        exact Nat.le_of_lt
          (by
            have lt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
            change BEDC.FKernel.ExternalBinary.bwordLength NatOne <
              BEDC.FKernel.ExternalBinary.bwordLength a at lt
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty] at lt
            exact lt)
    | inr same =>
        have len := congrArg BEDC.FKernel.ExternalBinary.bwordLength same
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
          BHist.Empty unary_empty] at len
        rw [len]
        exact Nat.le_refl 1
  have lengthB : 1 ≤ BEDC.FKernel.ExternalBinary.bwordLength b := by
    cases hb with
    | inl strict =>
        exact Nat.le_of_lt
          (by
            have lt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
            change BEDC.FKernel.ExternalBinary.bwordLength NatOne <
              BEDC.FKernel.ExternalBinary.bwordLength b at lt
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty] at lt
            exact lt)
    | inr same =>
        have len := congrArg BEDC.FKernel.ExternalBinary.bwordLength same
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
          BHist.Empty unary_empty] at len
        rw [len]
        exact Nat.le_refl 1
  by_cases unitLength :
      BEDC.FKernel.ExternalBinary.bwordLength (natMulFn a b) = 1
  · exact Or.inr
      ((BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
        productUnary (unary_e1_closed unary_empty)).mpr unitLength)
  · have productLength :
        BEDC.FKernel.ExternalBinary.bwordLength (natMulFn a b) =
          BEDC.FKernel.ExternalBinary.bwordLength a *
            BEDC.FKernel.ExternalBinary.bwordLength b :=
      natMulFn_bwordLength aUnary bUnary
    have oneLeProduct :
        1 ≤ BEDC.FKernel.ExternalBinary.bwordLength (natMulFn a b) := by
      rw [productLength]
      exact Nat.mul_le_mul lengthA lengthB
    have oneLtProduct :
        1 < BEDC.FKernel.ExternalBinary.bwordLength (natMulFn a b) :=
      Nat.lt_of_le_of_ne oneLeProduct (fun same => unitLength same.symm)
    exact Or.inl
      (NatUnaryStrictPrefix_of_length_lt (unary_e1_closed unary_empty)
        productUnary oneLtProduct)

def intOfNat (n : BHist) (hn : UnaryHistory n) : IntegerUp :=
  { sign := BMark.b0
    magnitude := n
    carrier := ⟨Or.inl rfl, hn⟩ }

def intOfNatWithSign (sign : BMark) (n : BHist) (hn : UnaryHistory n) : IntegerUp :=
  { sign := sign
    magnitude := n
    carrier := by
      cases sign
      · exact ⟨Or.inl rfl, hn⟩
      · exact ⟨Or.inr rfl, hn⟩ }

def intZero : IntegerUp :=
  intOfNat BHist.Empty unary_empty

def intOne : IntegerUp :=
  intOfNat NatOne (unary_e1_closed unary_empty)

def intToPair (z : IntegerUp) : BHist × BHist :=
  match z.sign with
  | BMark.b0 => (z.magnitude, BHist.Empty)
  | BMark.b1 => (BHist.Empty, z.magnitude)

theorem intToPair_carrier (z : IntegerUp) :
    IntPairCarrier (intToPair z).1 (intToPair z).2 := by
  cases z with
  | mk sign magnitude carrier =>
      cases sign
      · exact ⟨carrier.right, unary_empty⟩
      · exact ⟨unary_empty, carrier.right⟩

def pairSign (x : BHist × BHist) : BMark :=
  if natLeBool
      (BEDC.FKernel.ExternalBinary.bwordLength x.2)
      (BEDC.FKernel.ExternalBinary.bwordLength x.1)
    then BMark.b0 else BMark.b1

def pairMagnitude (x : BHist × BHist) : BHist :=
  if natLeBool
      (BEDC.FKernel.ExternalBinary.bwordLength x.2)
      (BEDC.FKernel.ExternalBinary.bwordLength x.1)
    then natToUnary
      (BEDC.FKernel.ExternalBinary.bwordLength x.1 -
        BEDC.FKernel.ExternalBinary.bwordLength x.2)
    else natToUnary
      (BEDC.FKernel.ExternalBinary.bwordLength x.2 -
        BEDC.FKernel.ExternalBinary.bwordLength x.1)

theorem pairMagnitude_unary (x : BHist × BHist) :
    UnaryHistory (pairMagnitude x) := by
  unfold pairMagnitude
  cases natLeBool
      (BEDC.FKernel.ExternalBinary.bwordLength x.2)
      (BEDC.FKernel.ExternalBinary.bwordLength x.1) <;>
    exact natToUnary_unary _

theorem pairSign_cases (x : BHist × BHist) :
    pairSign x = BMark.b0 ∨ pairSign x = BMark.b1 := by
  unfold pairSign
  cases natLeBool
      (BEDC.FKernel.ExternalBinary.bwordLength x.2)
      (BEDC.FKernel.ExternalBinary.bwordLength x.1)
  · exact Or.inr rfl
  · exact Or.inl rfl

def pairToInt (x : BHist × BHist) : IntegerUp :=
  { sign := pairSign x
    magnitude := pairMagnitude x
    carrier := ⟨pairSign_cases x, pairMagnitude_unary x⟩ }

def intAdd (x y : IntegerUp) : IntegerUp :=
  pairToInt (pairAdd (intToPair x) (intToPair y))

def intNeg (x : IntegerUp) : IntegerUp :=
  pairToInt (pairNeg (intToPair x))

def intMul (x y : IntegerUp) : IntegerUp :=
  pairToInt (pairMul (intToPair x) (intToPair y))

def intApart0 (x : IntegerUp) : Prop :=
  NatUnaryStrictPrefix NatOne x.magnitude ∨ hsame x.magnitude NatOne

theorem intApart0_magnitude_nonempty {x : IntegerUp} :
    intApart0 x -> hsame x.magnitude BHist.Empty -> False := by
  intro apart empty
  cases apart with
  | inl strict =>
      have oneLt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
      have magZero :
          BEDC.FKernel.ExternalBinary.bwordLength x.magnitude = 0 := by
        have emptyLen := congrArg BEDC.FKernel.ExternalBinary.bwordLength empty
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at emptyLen
        exact emptyLen
      rw [magZero] at oneLt
      cases oneLt
  | inr unit =>
      exact not_hsame_e1_empty (hsame_trans (hsame_symm unit) empty)

theorem intApart0_not_zero_pair {x : IntegerUp} :
    intApart0 x ->
      IntPairClassifier (intToPair x) (BHist.Empty, BHist.Empty) -> False := by
  intro apart zeroPair
  cases x with
  | mk sign magnitude carrier =>
      have magNonempty :
          hsame magnitude BHist.Empty -> False :=
        intApart0_magnitude_nonempty (x := { sign := sign, magnitude := magnitude, carrier := carrier })
          apart
      cases sign
      · have sameMag :
            hsame magnitude BHist.Empty :=
          (IntPairClassifier_zero_representative_criterion
            (p := magnitude) (n := BHist.Empty)
            carrier.right unary_empty).left.mp zeroPair
        exact magNonempty sameMag
      · have sameMag :
            hsame BHist.Empty magnitude :=
          (IntPairClassifier_zero_representative_criterion
            (p := BHist.Empty) (n := magnitude)
            unary_empty carrier.right).left.mp zeroPair
        exact magNonempty (hsame_symm sameMag)

def RatEq (x y : RatNum) : Prop :=
  IntPairClassifier
    (intToPair (intMul x.num (intOfNat y.den (ratDenCarrier y))))
    (intToPair (intMul y.num (intOfNat x.den (ratDenCarrier x))))

theorem RatEq_refl (x : RatNum) : RatEq x x := by
  unfold RatEq
  exact IntPairClassifier_equivalence_fields.right.right.left
    (intToPair_carrier (intMul x.num (intOfNat x.den (ratDenCarrier x))))

theorem RatEq_symm {x y : RatNum} : RatEq x y -> RatEq y x := by
  intro same
  unfold RatEq at same ⊢
  exact IntPairClassifier_equivalence_fields.right.right.right.left same

theorem RatEq_cross_carrier_left (x y : RatNum) :
    IntPairCarrier
      (intToPair (intMul x.num (intOfNat y.den (ratDenCarrier y)))).1
      (intToPair (intMul x.num (intOfNat y.den (ratDenCarrier y)))).2 :=
  intToPair_carrier _

theorem RatEq_cross_carrier_right (x y : RatNum) :
    IntPairCarrier
      (intToPair (intMul y.num (intOfNat x.den (ratDenCarrier x)))).1
      (intToPair (intMul y.num (intOfNat x.den (ratDenCarrier x)))).2 :=
  intToPair_carrier _

def intToRat (z : IntegerUp) : RatNum :=
  { num := z
    den := NatOne
    den_pos := Or.inr (hsame_refl NatOne) }

theorem intToRat_den (z : IntegerUp) : hsame (intToRat z).den NatOne := by
  rfl

def ratZero : RatNum := intToRat intZero

def ratOne : RatNum := intToRat intOne

def ratNeg (x : RatNum) : RatNum :=
  { num := intNeg x.num
    den := x.den
    den_pos := x.den_pos }

theorem ratNeg_den (x : RatNum) : hsame (ratNeg x).den x.den := by
  rfl

def ratMul (x y : RatNum) : RatNum :=
  { num := intMul x.num y.num
    den := natMulFn x.den y.den
    den_pos := ratDenPosMul x.den_pos y.den_pos }

theorem ratMul_den (x y : RatNum) :
    hsame (ratMul x y).den (natMulFn x.den y.den) := by
  rfl

def ratAdd (x y : RatNum) : RatNum :=
  { num :=
      intAdd
        (intMul x.num (intOfNat y.den (ratDenCarrier y)))
        (intMul y.num (intOfNat x.den (ratDenCarrier x)))
    den := natMulFn x.den y.den
    den_pos := ratDenPosMul x.den_pos y.den_pos }

theorem ratAdd_den (x y : RatNum) :
    hsame (ratAdd x y).den (natMulFn x.den y.den) := by
  rfl

def ratApart0 (x : RatNum) : Prop :=
  intApart0 x.num

def ratInvApart (x : RatNum) (hx : ratApart0 x) : RatNum :=
  match x with
  | RatNum.mk num den den_pos =>
  { num := intOfNatWithSign num.sign den (ratDenCarrier (RatNum.mk num den den_pos))
    den := num.magnitude
    den_pos := hx }

theorem ratInvApart_den {x : RatNum} (hx : ratApart0 x) :
    hsame (ratInvApart x hx).den x.num.magnitude := by
  cases x
  rfl

theorem ratInvApart_num_sign {x : RatNum} (hx : ratApart0 x) :
    (ratInvApart x hx).num.sign = x.num.sign := by
  cases x
  rfl

def ratValIndex (num den : BHist) : BHist × BHist :=
  (num, den)

def ratVal (p : BHist) (x : RatNum) (j : BHist × BHist) : Prop :=
  IsPadicValInt p (x.num.sign, x.num.magnitude) j.1 ∧
    IsPadicValInt p (BMark.b0, x.den) j.2 ∧
      IntPairCarrier j.1 j.2

theorem ratVal_components {p : BHist} {x : RatNum} {j : BHist × BHist} :
    IsPadicValInt p (x.num.sign, x.num.magnitude) j.1 ->
      IsPadicValInt p (BMark.b0, x.den) j.2 ->
        IntPairCarrier j.1 j.2 ->
          ratVal p x j := by
  intro numVal denVal carrier
  exact ⟨numVal, denVal, carrier⟩

def ratValAdd (j k : BHist × BHist) : BHist × BHist :=
  pairAdd j k

def ratMagnitude (x : RatNum) : RatNum :=
  { num := intOfNat x.num.magnitude x.num.carrier.right
    den := x.den
    den_pos := x.den_pos }

theorem ratMagnitude_den (x : RatNum) :
    hsame (ratMagnitude x).den x.den := by
  exact hsame_refl x.den

theorem ratMagnitude_num_nonnegative (x : RatNum) :
    (ratMagnitude x).num.sign = BMark.b0 := by
  rfl

theorem ratMagnitude_num_magnitude (x : RatNum) :
    hsame (ratMagnitude x).num.magnitude x.num.magnitude := by
  rfl

end BEDC.Derived.RationalUp
