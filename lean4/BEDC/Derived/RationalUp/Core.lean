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
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
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

def IntEq (x y : IntegerUp) : Prop :=
  IntPairClassifier (intToPair x) (intToPair y)

def IntNonzero (x : IntegerUp) : Prop :=
  intApart0 x

def IntMul (x y : IntegerUp) : IntegerUp :=
  intMul x y

private theorem natLeBool_true_to_le {a b : Nat} :
    natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem natLeBool_false_to_lt {a b : Nat} :
    natLeBool a b = false -> b < a := by
  induction a generalizing b with
  | zero =>
      intro h
      cases b <;> cases h
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          exact Nat.succ_pos a
      | succ b =>
          exact Nat.succ_lt_succ (ih h)

private theorem nat_sub_add_cancel_of_le {a b : Nat} :
    b ≤ a -> a - b + b = a := by
  induction b generalizing a with
  | zero =>
      intro _h
      rw [Nat.sub_zero, Nat.add_zero]
  | succ b ih =>
      intro h
      cases a with
      | zero =>
          cases h
      | succ a =>
          rw [Nat.succ_sub_succ, Nat.add_succ]
          exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem nat_add_sub_cancel_left_of_le {a b : Nat} :
    a ≤ b -> a + (b - a) = b := by
  intro h
  calc
    a + (b - a) = b - a + a := Nat.add_comm a (b - a)
    _ = b := nat_sub_add_cancel_of_le h

theorem IntPairClassifier_length_eq {x y : BHist × BHist} :
    IntPairClassifier x y ->
      bwordLength x.1 + bwordLength y.2 =
        bwordLength y.1 + bwordLength x.2 := by
  intro classified
  have sameLength := congrArg bwordLength classified.right.right
  rw [bwordLength_append x.1 y.2] at sameLength
  rw [bwordLength_append y.1 x.2] at sameLength
  exact sameLength

theorem IntPairClassifier_of_length_eq {x y : BHist × BHist}
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    bwordLength x.1 + bwordLength y.2 =
        bwordLength y.1 + bwordLength x.2 ->
      IntPairClassifier x y := by
  intro lengthEq
  have leftUnary : UnaryHistory (append x.1 y.2) :=
    unary_append_closed hx.left hy.right
  have rightUnary : UnaryHistory (append y.1 x.2) :=
    unary_append_closed hy.left hx.right
  have appendLength :
      bwordLength (append x.1 y.2) = bwordLength (append y.1 x.2) := by
    rw [bwordLength_append x.1 y.2]
    rw [bwordLength_append y.1 x.2]
    exact lengthEq
  exact ⟨hx, hy,
    (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
      leftUnary rightUnary).mpr appendLength⟩

theorem intApart0_length_pos {x : IntegerUp} :
    intApart0 x -> 0 < bwordLength x.magnitude := by
  intro apart
  cases apart with
  | inl strict =>
      have oneLt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
      have oneLen :
          bwordLength NatOne = 1 :=
        BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
          BHist.Empty unary_empty
      rw [oneLen] at oneLt
      exact Nat.lt_trans (Nat.zero_lt_succ 0) oneLt
  | inr unit =>
      have unitLen := congrArg bwordLength unit
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
        BHist.Empty unary_empty] at unitLen
      rw [unitLen]
      exact Nat.zero_lt_succ 0

theorem intToPair_pairToInt_classifier (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (intToPair (pairToInt x)) x := by
  cases x with
  | mk p n =>
      have hx' : IntPairCarrier p n := by
        simpa using hx
      change
        IntPairClassifier
          (match pairSign (p, n) with
          | BMark.b0 => (pairMagnitude (p, n), BHist.Empty)
          | BMark.b1 => (BHist.Empty, pairMagnitude (p, n)))
          (p, n)
      by_cases branchTrue : natLeBool (bwordLength n) (bwordLength p) = true
      · have nLeP : bwordLength n ≤ bwordLength p :=
          natLeBool_true_to_le branchTrue
        have carrierLeft :
            IntPairCarrier
              (natToUnary (bwordLength p - bwordLength n)) BHist.Empty :=
          ⟨natToUnary_unary _, unary_empty⟩
        have core :
            IntPairClassifier
              (natToUnary (bwordLength p - bwordLength n), BHist.Empty) (p, n) := by
          apply IntPairClassifier_of_length_eq carrierLeft hx'
          rw [natToUnary_length]
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [Nat.add_zero]
          exact nat_sub_add_cancel_of_le nLeP
        change
          IntPairClassifier
            (match
              if natLeBool (bwordLength n) (bwordLength p) then
                BMark.b0 else BMark.b1 with
            | BMark.b0 =>
                (if natLeBool (bwordLength n) (bwordLength p) then
                    natToUnary (bwordLength p - bwordLength n)
                  else natToUnary (bwordLength n - bwordLength p),
                  BHist.Empty)
            | BMark.b1 =>
                (BHist.Empty,
                  if natLeBool (bwordLength n) (bwordLength p) then
                    natToUnary (bwordLength p - bwordLength n)
                  else natToUnary (bwordLength n - bwordLength p)))
            (p, n)
        rw [branchTrue]
        exact core
      · have branchFalse :
            natLeBool (bwordLength n) (bwordLength p) = false := by
          cases hbranch : natLeBool (bwordLength n) (bwordLength p) with
          | false => rfl
          | true => exact False.elim (branchTrue hbranch)
        have pLtN : bwordLength p < bwordLength n :=
          natLeBool_false_to_lt branchFalse
        have pLeN : bwordLength p ≤ bwordLength n :=
          Nat.le_of_lt pLtN
        have carrierLeft :
            IntPairCarrier BHist.Empty
              (natToUnary (bwordLength n - bwordLength p)) :=
          ⟨unary_empty, natToUnary_unary _⟩
        have core :
            IntPairClassifier
              (BHist.Empty, natToUnary (bwordLength n - bwordLength p)) (p, n) := by
          apply IntPairClassifier_of_length_eq carrierLeft hx'
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [natToUnary_length]
          rw [Nat.zero_add]
          exact (nat_add_sub_cancel_left_of_le pLeN).symm
        change
          IntPairClassifier
            (match
              if natLeBool (bwordLength n) (bwordLength p) then
                BMark.b0 else BMark.b1 with
            | BMark.b0 =>
                (if natLeBool (bwordLength n) (bwordLength p) then
                    natToUnary (bwordLength p - bwordLength n)
                  else natToUnary (bwordLength n - bwordLength p),
                  BHist.Empty)
            | BMark.b1 =>
                (BHist.Empty,
                  if natLeBool (bwordLength n) (bwordLength p) then
                    natToUnary (bwordLength p - bwordLength n)
                  else natToUnary (bwordLength n - bwordLength p)))
            (p, n)
        rw [branchFalse]
        exact core

theorem intMul_pair_classifier (x y : IntegerUp) :
    IntPairClassifier (intToPair (intMul x y)) (pairMul (intToPair x) (intToPair y)) := by
  unfold intMul
  exact intToPair_pairToInt_classifier _
    (pairMul_carrier (intToPair_carrier x) (intToPair_carrier y))

private theorem natMulFn_empty_left_hsame {q : BHist} :
    UnaryHistory q -> hsame (natMulFn BHist.Empty q) BHist.Empty := by
  intro qUnary
  exact NatMul_empty_left_result_empty (natMulFn_rel unary_empty qUnary)

private theorem natMulFn_length_eq_mul (d q : BHist)
    (hd : UnaryHistory d) (hq : UnaryHistory q) :
    bwordLength (natMulFn d q) = bwordLength d * bwordLength q :=
  natMulFn_bwordLength hd hq

theorem IntMul_left_cancel {c a b : IntegerUp} :
    IntNonzero c -> IntEq (IntMul c a) (IntMul c b) -> IntEq a b := by
  intro cNonzero sameProduct
  change intApart0 c at cNonzero
  change IntPairClassifier (intToPair (intMul c a)) (intToPair (intMul c b)) at sameProduct
  change IntPairClassifier (intToPair a) (intToPair b)
  have leftProduct := intMul_pair_classifier c a
  have rightProduct := intMul_pair_classifier c b
  have pairProductSame :
      IntPairClassifier (pairMul (intToPair c) (intToPair a))
        (pairMul (intToPair c) (intToPair b)) := by
    exact IntPairClassifier_equivalence_fields.right.right.right.right.left
      (IntPairClassifier_equivalence_fields.right.right.right.left leftProduct)
      (IntPairClassifier_equivalence_fields.right.right.right.right.left
        sameProduct rightProduct)
  cases c with
  | mk cSign cMagnitude cCarrier =>
      cases cSign with
      | b0 =>
          let ap := (intToPair a).1
          let an := (intToPair a).2
          let bp := (intToPair b).1
          let bn := (intToPair b).2
          have aCarrier := intToPair_carrier a
          have bCarrier := intToPair_carrier b
          have productLength := IntPairClassifier_length_eq pairProductSame
          have cPositive : 0 < bwordLength cMagnitude :=
            intApart0_length_pos (x := { sign := BMark.b0, magnitude := cMagnitude, carrier := cCarrier })
              cNonzero
          have reducedLength :
              bwordLength ap + bwordLength bn =
                bwordLength bp + bwordLength an := by
            have productLength' :
                bwordLength cMagnitude * (bwordLength ap + bwordLength bn) =
                  bwordLength cMagnitude * (bwordLength bp + bwordLength an) := by
              calc
                bwordLength cMagnitude * (bwordLength ap + bwordLength bn)
                    = bwordLength cMagnitude * bwordLength ap +
                        bwordLength cMagnitude * bwordLength bn :=
                      Nat.left_distrib (bwordLength cMagnitude)
                        (bwordLength ap) (bwordLength bn)
                _ =
                    (bwordLength (natMulFn cMagnitude ap) +
                        bwordLength (natMulFn BHist.Empty an)) +
                      (bwordLength (natMulFn cMagnitude bn) +
                        bwordLength (natMulFn BHist.Empty bp)) := by
                      rw [natMulFn_length_eq_mul cMagnitude ap cCarrier.right aCarrier.left]
                      rw [natMulFn_length_eq_mul cMagnitude bn cCarrier.right bCarrier.right]
                      rw [natMulFn_length_eq_mul BHist.Empty an unary_empty aCarrier.right]
                      rw [natMulFn_length_eq_mul BHist.Empty bp unary_empty bCarrier.left]
                      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
                      rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
                _ =
                    (bwordLength (append (natMulFn cMagnitude ap)
                        (natMulFn BHist.Empty an))) +
                      (bwordLength (append (natMulFn cMagnitude bn)
                        (natMulFn BHist.Empty bp))) := by
                      rw [bwordLength_append, bwordLength_append]
                _ =
                    (bwordLength (append (natMulFn cMagnitude bp)
                        (natMulFn BHist.Empty bn))) +
                      (bwordLength (append (natMulFn cMagnitude an)
                        (natMulFn BHist.Empty ap))) := productLength
                _ =
                    (bwordLength (natMulFn cMagnitude bp) +
                        bwordLength (natMulFn BHist.Empty bn)) +
                      (bwordLength (natMulFn cMagnitude an) +
                        bwordLength (natMulFn BHist.Empty ap)) := by
                      rw [bwordLength_append, bwordLength_append]
                _ =
                    bwordLength cMagnitude * bwordLength bp +
                      bwordLength cMagnitude * bwordLength an := by
                      rw [natMulFn_length_eq_mul cMagnitude bp cCarrier.right bCarrier.left]
                      rw [natMulFn_length_eq_mul cMagnitude an cCarrier.right aCarrier.right]
                      rw [natMulFn_length_eq_mul BHist.Empty bn unary_empty bCarrier.right]
                      rw [natMulFn_length_eq_mul BHist.Empty ap unary_empty aCarrier.left]
                      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
                      rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
                _ = bwordLength cMagnitude * (bwordLength bp + bwordLength an) :=
                      (Nat.left_distrib (bwordLength cMagnitude)
                        (bwordLength bp) (bwordLength an)).symm
            exact Nat.eq_of_mul_eq_mul_left cPositive productLength'
          exact IntPairClassifier_of_length_eq aCarrier bCarrier reducedLength
      | b1 =>
          let ap := (intToPair a).1
          let an := (intToPair a).2
          let bp := (intToPair b).1
          let bn := (intToPair b).2
          have aCarrier := intToPair_carrier a
          have bCarrier := intToPair_carrier b
          have productLength := IntPairClassifier_length_eq pairProductSame
          have cPositive : 0 < bwordLength cMagnitude :=
            intApart0_length_pos (x := { sign := BMark.b1, magnitude := cMagnitude, carrier := cCarrier })
              cNonzero
          have reducedLength :
              bwordLength ap + bwordLength bn =
                bwordLength bp + bwordLength an := by
            have productLength' :
                bwordLength cMagnitude * (bwordLength an + bwordLength bp) =
                  bwordLength cMagnitude * (bwordLength bn + bwordLength ap) := by
              calc
                bwordLength cMagnitude * (bwordLength an + bwordLength bp)
                    = bwordLength cMagnitude * bwordLength an +
                        bwordLength cMagnitude * bwordLength bp :=
                      Nat.left_distrib (bwordLength cMagnitude)
                        (bwordLength an) (bwordLength bp)
                _ =
                    (bwordLength (natMulFn BHist.Empty ap) +
                        bwordLength (natMulFn cMagnitude an)) +
                      (bwordLength (natMulFn BHist.Empty bn) +
                        bwordLength (natMulFn cMagnitude bp)) := by
                      rw [natMulFn_length_eq_mul cMagnitude an cCarrier.right aCarrier.right]
                      rw [natMulFn_length_eq_mul cMagnitude bp cCarrier.right bCarrier.left]
                      rw [natMulFn_length_eq_mul BHist.Empty ap unary_empty aCarrier.left]
                      rw [natMulFn_length_eq_mul BHist.Empty bn unary_empty bCarrier.right]
                      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
                      rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.zero_add]
                _ =
                    (bwordLength (append (natMulFn BHist.Empty ap)
                        (natMulFn cMagnitude an))) +
                      (bwordLength (append (natMulFn BHist.Empty bn)
                        (natMulFn cMagnitude bp))) := by
                      rw [bwordLength_append, bwordLength_append]
                _ =
                    (bwordLength (append (natMulFn BHist.Empty bp)
                        (natMulFn cMagnitude bn))) +
                      (bwordLength (append (natMulFn BHist.Empty an)
                        (natMulFn cMagnitude ap))) := productLength
                _ =
                    (bwordLength (natMulFn BHist.Empty bp) +
                        bwordLength (natMulFn cMagnitude bn)) +
                      (bwordLength (natMulFn BHist.Empty an) +
                        bwordLength (natMulFn cMagnitude ap)) := by
                      rw [bwordLength_append, bwordLength_append]
                _ =
                    bwordLength cMagnitude * bwordLength bn +
                      bwordLength cMagnitude * bwordLength ap := by
                      rw [natMulFn_length_eq_mul cMagnitude bn cCarrier.right bCarrier.right]
                      rw [natMulFn_length_eq_mul cMagnitude ap cCarrier.right aCarrier.left]
                      rw [natMulFn_length_eq_mul BHist.Empty bp unary_empty bCarrier.left]
                      rw [natMulFn_length_eq_mul BHist.Empty an unary_empty aCarrier.right]
                      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
                      rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.zero_add]
                _ = bwordLength cMagnitude * (bwordLength bn + bwordLength ap) :=
                      (Nat.left_distrib (bwordLength cMagnitude)
                        (bwordLength bn) (bwordLength ap)).symm
            have swapped :
                bwordLength an + bwordLength bp =
                  bwordLength bn + bwordLength ap :=
              Nat.eq_of_mul_eq_mul_left cPositive productLength'
            calc
              bwordLength ap + bwordLength bn =
                  bwordLength bn + bwordLength ap := Nat.add_comm _ _
              _ = bwordLength an + bwordLength bp := swapped.symm
              _ = bwordLength bp + bwordLength an := Nat.add_comm _ _
          exact IntPairClassifier_of_length_eq aCarrier bCarrier reducedLength

theorem pairMul_comm (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    IntPairClassifier (pairMul x y) (pairMul y x) := by
  apply IntPairClassifier_of_length_eq (pairMul_carrier hx hy) (pairMul_carrier hy hx)
  rw [pairMul]
  rw [pairMul]
  rw [bwordLength_append, bwordLength_append, bwordLength_append, bwordLength_append]
  rw [natMulFn_bwordLength hx.left hy.left]
  rw [natMulFn_bwordLength hx.right hy.right]
  rw [natMulFn_bwordLength hx.left hy.right]
  rw [natMulFn_bwordLength hx.right hy.left]
  rw [natMulFn_bwordLength hy.left hx.left]
  rw [natMulFn_bwordLength hy.right hx.right]
  rw [natMulFn_bwordLength hy.left hx.right]
  rw [natMulFn_bwordLength hy.right hx.left]
  rw [Nat.mul_comm (bwordLength y.1) (bwordLength x.1)]
  rw [Nat.mul_comm (bwordLength y.2) (bwordLength x.2)]
  rw [Nat.mul_comm (bwordLength y.1) (bwordLength x.2)]
  rw [Nat.mul_comm (bwordLength y.2) (bwordLength x.1)]
  exact congrArg
    (fun t =>
      (bwordLength x.1 * bwordLength y.1 +
          bwordLength x.2 * bwordLength y.2) + t)
    (Nat.add_comm (bwordLength x.2 * bwordLength y.1)
      (bwordLength x.1 * bwordLength y.2))

theorem IntMul_comm (a b : IntegerUp) :
    IntEq (IntMul a b) (IntMul b a) := by
  unfold IntEq IntMul
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intMul_pair_classifier a b)
    (IntPairClassifier_equivalence_fields.right.right.right.right.left
      (pairMul_comm (intToPair a) (intToPair b) (intToPair_carrier a) (intToPair_carrier b))
      (IntPairClassifier_equivalence_fields.right.right.right.left
        (intMul_pair_classifier b a)))

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
