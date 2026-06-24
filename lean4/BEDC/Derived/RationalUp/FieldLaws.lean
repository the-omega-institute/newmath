import BEDC.Derived.RationalUp.RatLaws

namespace BEDC.Derived.RationalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp

private theorem nat_add_pair_comm (a b c d : Nat) :
    (a + b) + (d + c) = (b + a) + (c + d) := by
  calc
    (a + b) + (d + c) = (a + b) + (c + d) :=
      congrArg (fun t => (a + b) + t) (Nat.add_comm d c)
    _ = (b + a) + (c + d) :=
      congrArg (fun t => t + (c + d)) (Nat.add_comm a b)

private theorem nat_add_pair_assoc (a b c d e f : Nat) :
    ((a + b) + c) + (d + (e + f)) =
      (a + (b + c)) + ((d + e) + f) := by
  calc
    ((a + b) + c) + (d + (e + f)) =
        (a + (b + c)) + (d + (e + f)) :=
      congrArg (fun t => t + (d + (e + f))) (Nat.add_assoc a b c)
    _ = (a + (b + c)) + ((d + e) + f) :=
      congrArg (fun t => (a + (b + c)) + t) (Nat.add_assoc d e f).symm

private theorem nat_add_zero_pair (a b : Nat) :
    (a + 0) + b = a + b := by
  rw [Nat.add_zero]

private theorem nat_add_pair_neg (a b : Nat) :
    (a + b) + (a + b) = (a + b) + (b + a) := by
  rw [Nat.add_comm b a]

theorem intMul_two_by_two_swap (a b c d : IntegerUp) :
    IntEq (IntMul (IntMul a b) (IntMul c d))
      (IntMul (IntMul a c) (IntMul b d)) := by
  exact IntEq_trans (intMul_assoc a b (IntMul c d))
    (IntEq_trans
      (intMul_left_congr (c := a)
        (IntEq_trans (intMul_rotate_left b c d) (intMul_assoc c b d)))
      (IntEq_symm (intMul_assoc a c (IntMul b d))))

theorem pairAdd_comm (x y : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) (hy : IntPairCarrier y.1 y.2) :
    IntPairClassifier (pairAdd x y) (pairAdd y x) := by
  apply IntPairClassifier_of_length_eq
    (pairAdd_carrier hx hy) (pairAdd_carrier hy hx)
  rw [pairAdd_pos_length x y hx hy]
  rw [pairAdd_neg_length y x hy hx]
  rw [pairAdd_pos_length y x hy hx]
  rw [pairAdd_neg_length x y hx hy]
  exact nat_add_pair_comm
    (bwordLength x.1) (bwordLength y.1)
    (bwordLength x.2) (bwordLength y.2)

theorem intAdd_comm (a b : IntegerUp) :
    IntEq (IntAdd a b) (IntAdd b a) := by
  unfold IntEq IntAdd
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intAdd_pair_classifier a b)
    (IntPairClassifier_equivalence_fields.right.right.right.right.left
      (pairAdd_comm (intToPair a) (intToPair b)
        (intToPair_carrier a) (intToPair_carrier b))
      (IntPairClassifier_equivalence_fields.right.right.right.left
        (intAdd_pair_classifier b a)))

theorem pairAdd_assoc (x y z : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2)
    (hy : IntPairCarrier y.1 y.2)
    (hz : IntPairCarrier z.1 z.2) :
    IntPairClassifier (pairAdd (pairAdd x y) z)
      (pairAdd x (pairAdd y z)) := by
  apply IntPairClassifier_of_length_eq
    (pairAdd_carrier (pairAdd_carrier hx hy) hz)
    (pairAdd_carrier hx (pairAdd_carrier hy hz))
  rw [pairAdd_pos_length (pairAdd x y) z (pairAdd_carrier hx hy) hz]
  rw [pairAdd_neg_length x (pairAdd y z) hx (pairAdd_carrier hy hz)]
  rw [pairAdd_pos_length x y hx hy]
  rw [pairAdd_neg_length y z hy hz]
  rw [pairAdd_pos_length x (pairAdd y z) hx (pairAdd_carrier hy hz)]
  rw [pairAdd_neg_length (pairAdd x y) z (pairAdd_carrier hx hy) hz]
  rw [pairAdd_pos_length y z hy hz]
  rw [pairAdd_neg_length x y hx hy]
  exact nat_add_pair_assoc
    (bwordLength x.1) (bwordLength y.1) (bwordLength z.1)
    (bwordLength x.2) (bwordLength y.2) (bwordLength z.2)

theorem intAdd_assoc (a b c : IntegerUp) :
    IntEq (IntAdd (IntAdd a b) c) (IntAdd a (IntAdd b c)) := by
  unfold IntEq IntAdd
  have leftOuter := intAdd_pair_classifier (intAdd a b) c
  have leftInner := intAdd_pair_classifier a b
  have leftTransport :
      IntPairClassifier
        (pairAdd (intToPair (intAdd a b)) (intToPair c))
        (pairAdd (pairAdd (intToPair a) (intToPair b)) (intToPair c)) :=
    pairAdd_classifier_congr leftInner
      (IntPairClassifier_equivalence_fields.right.right.left (intToPair_carrier c))
  have assocPair :
      IntPairClassifier
        (pairAdd (pairAdd (intToPair a) (intToPair b)) (intToPair c))
        (pairAdd (intToPair a) (pairAdd (intToPair b) (intToPair c))) :=
    pairAdd_assoc (intToPair a) (intToPair b) (intToPair c)
      (intToPair_carrier a) (intToPair_carrier b) (intToPair_carrier c)
  have rightInner := intAdd_pair_classifier b c
  have rightTransport :
      IntPairClassifier
        (pairAdd (intToPair a) (pairAdd (intToPair b) (intToPair c)))
        (pairAdd (intToPair a) (intToPair (intAdd b c))) :=
    pairAdd_classifier_congr
      (IntPairClassifier_equivalence_fields.right.right.left (intToPair_carrier a))
      (IntPairClassifier_equivalence_fields.right.right.right.left rightInner)
  have rightOuter := intAdd_pair_classifier a (intAdd b c)
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left leftTransport
      (IntPairClassifier_equivalence_fields.right.right.right.right.left assocPair
        (IntPairClassifier_equivalence_fields.right.right.right.right.left rightTransport
          (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))))

theorem intAdd_right_congr {a b c : IntegerUp} :
    IntEq a b -> IntEq (IntAdd a c) (IntAdd b c) := by
  intro same
  unfold IntEq at same
  unfold IntEq IntAdd
  have leftOuter := intAdd_pair_classifier a c
  have transport :
      IntPairClassifier
        (pairAdd (intToPair a) (intToPair c))
        (pairAdd (intToPair b) (intToPair c)) :=
    pairAdd_classifier_congr same
      (IntPairClassifier_equivalence_fields.right.right.left (intToPair_carrier c))
  have rightOuter := intAdd_pair_classifier b c
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left leftOuter
    (IntPairClassifier_equivalence_fields.right.right.right.right.left transport
      (IntPairClassifier_equivalence_fields.right.right.right.left rightOuter))

theorem intAdd_left_congr {a b c : IntegerUp} :
    IntEq a b -> IntEq (IntAdd c a) (IntAdd c b) := by
  intro same
  exact IntEq_trans (intAdd_comm c a)
    (IntEq_trans (intAdd_right_congr same) (intAdd_comm b c))

theorem pairAdd_zero_right (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (pairAdd x (BHist.Empty, BHist.Empty)) x := by
  apply IntPairClassifier_of_length_eq
    (pairAdd_carrier hx ⟨unary_empty, unary_empty⟩) hx
  rw [pairAdd_pos_length x (BHist.Empty, BHist.Empty) hx
    ⟨unary_empty, unary_empty⟩]
  rw [pairAdd_neg_length x (BHist.Empty, BHist.Empty) hx
    ⟨unary_empty, unary_empty⟩]
  rw [NatUp_unary_standard_bridge.left]
  exact nat_add_zero_pair (bwordLength x.1) (bwordLength x.2)

theorem pairAdd_neg_right (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (pairAdd x (pairNeg x)) (BHist.Empty, BHist.Empty) := by
  apply IntPairClassifier_of_length_eq
    (pairAdd_carrier hx (pairNeg_carrier hx)) ⟨unary_empty, unary_empty⟩
  rw [pairAdd_pos_length x (pairNeg x) hx (pairNeg_carrier hx)]
  rw [pairAdd_neg_length x (pairNeg x) hx (pairNeg_carrier hx)]
  rw [NatUp_unary_standard_bridge.left]
  change (bwordLength x.1 + bwordLength x.2) + 0 =
    0 + (bwordLength x.2 + bwordLength x.1)
  rw [Nat.add_zero, Nat.zero_add]
  exact Nat.add_comm (bwordLength x.1) (bwordLength x.2)

theorem intAdd_zero_right (a : IntegerUp) :
    IntEq (IntAdd a intZero) a := by
  unfold IntEq IntAdd intZero intOfNat
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intAdd_pair_classifier a
      { sign := BMark.b0, magnitude := BHist.Empty,
        carrier := ⟨Or.inl rfl, unary_empty⟩ })
    (pairAdd_zero_right (intToPair a) (intToPair_carrier a))

theorem intAdd_zero_left (a : IntegerUp) :
    IntEq (IntAdd intZero a) a := by
  exact IntEq_trans (intAdd_comm intZero a) (intAdd_zero_right a)

theorem intAdd_neg_right (a : IntegerUp) :
    IntEq (IntAdd a (intNeg a)) intZero := by
  unfold IntEq IntAdd intNeg intZero intOfNat
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intAdd_pair_classifier a (pairToInt (pairNeg (intToPair a))))
    (IntPairClassifier_equivalence_fields.right.right.right.right.left
      (pairAdd_classifier_congr
        (IntPairClassifier_equivalence_fields.right.right.left (intToPair_carrier a))
        (intToPair_pairToInt_classifier (pairNeg (intToPair a))
          (pairNeg_carrier (intToPair_carrier a))))
      (pairAdd_neg_right (intToPair a) (intToPair_carrier a)))

theorem intAdd_neg_left (a : IntegerUp) :
    IntEq (IntAdd (intNeg a) a) intZero := by
  exact IntEq_trans (intAdd_comm (intNeg a) a) (intAdd_neg_right a)

theorem pairMul_zero_right (x : BHist × BHist)
    (hx : IntPairCarrier x.1 x.2) :
    IntPairClassifier (pairMul x (BHist.Empty, BHist.Empty))
      (BHist.Empty, BHist.Empty) := by
  apply IntPairClassifier_of_length_eq
    (pairMul_carrier hx ⟨unary_empty, unary_empty⟩)
    ⟨unary_empty, unary_empty⟩
  rw [pairMul_pos_length x (BHist.Empty, BHist.Empty) hx
    ⟨unary_empty, unary_empty⟩]
  rw [pairMul_neg_length x (BHist.Empty, BHist.Empty) hx
    ⟨unary_empty, unary_empty⟩]
  rw [NatUp_unary_standard_bridge.left]
  rw [Nat.mul_zero, Nat.mul_zero]

theorem intMul_zero_right (a : IntegerUp) :
    IntEq (IntMul a intZero) intZero := by
  unfold IntEq IntMul intZero intOfNat
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    (intMul_pair_classifier a
      { sign := BMark.b0, magnitude := BHist.Empty,
        carrier := ⟨Or.inl rfl, unary_empty⟩ })
    (pairMul_zero_right (intToPair a) (intToPair_carrier a))

theorem intMul_zero_left (a : IntegerUp) :
    IntEq (IntMul intZero a) intZero := by
  exact IntEq_trans (IntMul_comm intZero a) (intMul_zero_right a)

theorem intOfNat_natMul_as_intMul
    (a b : BHist) (ha : UnaryHistory a) (hb : UnaryHistory b)
    (hab : UnaryHistory (natMulFn a b)) :
    IntEq (intOfNat (natMulFn a b) hab)
      (IntMul (intOfNat a ha) (intOfNat b hb)) := by
  exact IntEq_trans
    (intOfNat_hsame_congr hab (natMulFn_unary ha hb) (hsame_refl _))
    (IntEq_symm (intMul_same_sign_nat BMark.b0 a b ha hb))

def ratDenInt (x : RatNum) : IntegerUp :=
  intOfNat x.den (ratDenCarrier x)

theorem ratDenInt_nonzero (x : RatNum) :
    IntNonzero (ratDenInt x) := by
  unfold ratDenInt
  exact intOfNat_nonzero_of_den x

theorem ratDenInt_mul (x y : RatNum) :
    IntEq (ratDenInt (ratMul x y))
      (IntMul (ratDenInt x) (ratDenInt y)) := by
  unfold ratDenInt ratMul
  exact intOfNat_natMul_as_intMul x.den y.den
    (ratDenCarrier x) (ratDenCarrier y)
    (ratDenCarrier
      { num := intMul x.num y.num,
        den := natMulFn x.den y.den,
        den_pos := ratDenPosMul x.den_pos y.den_pos })

theorem ratDenInt_add (x y : RatNum) :
    IntEq (ratDenInt (ratAdd x y))
      (IntMul (ratDenInt x) (ratDenInt y)) := by
  unfold ratDenInt ratAdd
  exact intOfNat_natMul_as_intMul x.den y.den
    (ratDenCarrier x) (ratDenCarrier y)
    (ratDenCarrier
      { num :=
          intAdd
            (intMul x.num (intOfNat y.den (ratDenCarrier y)))
            (intMul y.num (intOfNat x.den (ratDenCarrier x))),
        den := natMulFn x.den y.den,
        den_pos := ratDenPosMul x.den_pos y.den_pos })

theorem ratDenInt_one : IntEq (ratDenInt ratOne) intOne := by
  unfold ratDenInt ratOne intToRat intOne
  exact IntEq_refl (intOfNat NatOne (unary_e1_closed unary_empty))

theorem ratDenInt_zero : IntEq (ratDenInt ratZero) intOne := by
  unfold ratDenInt ratZero intToRat intOne
  exact IntEq_refl (intOfNat NatOne (unary_e1_closed unary_empty))

theorem ratEq_of_num_den_intEq {x y : RatNum} :
    IntEq x.num y.num -> IntEq (ratDenInt x) (ratDenInt y) ->
      RatEq x y := by
  intro numEq denEq
  unfold RatEq
  change IntEq (IntMul x.num (ratDenInt y)) (IntMul y.num (ratDenInt x))
  exact IntEq_trans (intMul_right_congr numEq)
    (intMul_left_congr (IntEq_symm denEq))

theorem ratAdd_comm (x y : RatNum) :
    RatEq (ratAdd x y) (ratAdd y x) := by
  apply ratEq_of_num_den_intEq
  · unfold ratAdd
    exact intAdd_comm
      (intMul x.num (intOfNat y.den (ratDenCarrier y)))
      (intMul y.num (intOfNat x.den (ratDenCarrier x)))
  · exact IntEq_trans (ratDenInt_add x y)
      (IntEq_trans (IntMul_comm (ratDenInt x) (ratDenInt y))
        (IntEq_symm (ratDenInt_add y x)))

theorem ratAdd_zero_right (x : RatNum) :
    RatEq (ratAdd x ratZero) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratAdd ratZero intToRat
    change IntEq
      (IntAdd (IntMul x.num (intOfNat NatOne (unary_e1_closed unary_empty)))
        (IntMul intZero (intOfNat x.den (ratDenCarrier x)))) x.num
    exact IntEq_trans
      (intAdd_left_congr (intMul_zero_left (intOfNat x.den (ratDenCarrier x))))
      (IntEq_trans
        (intAdd_zero_right (IntMul x.num
          (intOfNat NatOne (unary_e1_closed unary_empty))))
        (intMul_one_right x.num))
  · exact IntEq_trans (ratDenInt_add x ratZero)
      (IntEq_trans
        (intMul_left_congr ratDenInt_zero)
        (intMul_one_right (ratDenInt x)))

theorem ratZero_add_left (x : RatNum) :
    RatEq (ratAdd ratZero x) x := by
  exact RatEq_trans (ratAdd ratZero x) (ratAdd x ratZero) x
    (ratAdd_comm ratZero x) (ratAdd_zero_right x)

theorem ratMul_respects {x x' y y' : RatNum} :
    RatEq x x' -> RatEq y y' ->
      RatEq (ratMul x y) (ratMul x' y') := by
  intro hx hy
  have hxInt : IntEq (IntMul x.num (ratDenInt x'))
      (IntMul x'.num (ratDenInt x)) := by
    unfold RatEq at hx
    unfold IntEq IntMul ratDenInt
    exact hx
  have hyInt : IntEq (IntMul y.num (ratDenInt y'))
      (IntMul y'.num (ratDenInt y)) := by
    unfold RatEq at hy
    unfold IntEq IntMul ratDenInt
    exact hy
  unfold RatEq
  change IntEq
    (IntMul (IntMul x.num y.num) (ratDenInt (ratMul x' y')))
    (IntMul (IntMul x'.num y'.num) (ratDenInt (ratMul x y)))
  have denLeft :
      IntEq
        (ratDenInt (ratMul x' y'))
        (IntMul (ratDenInt x') (ratDenInt y')) :=
    ratDenInt_mul x' y'
  have denRight :
      IntEq
        (ratDenInt (ratMul x y))
        (IntMul (ratDenInt x) (ratDenInt y)) :=
    ratDenInt_mul x y
  have leftToStructured :
      IntEq
        (IntMul (IntMul x.num y.num) (ratDenInt (ratMul x' y')))
        (IntMul (IntMul x.num y.num)
          (IntMul (ratDenInt x') (ratDenInt y'))) :=
    intMul_left_congr denLeft
  have rightToStructured :
      IntEq
        (IntMul (IntMul x'.num y'.num) (ratDenInt (ratMul x y)))
        (IntMul (IntMul x'.num y'.num)
          (IntMul (ratDenInt x) (ratDenInt y))) :=
    intMul_left_congr denRight
  have structured :
      IntEq
        (IntMul (IntMul x.num y.num)
          (IntMul (ratDenInt x') (ratDenInt y')))
        (IntMul (IntMul x'.num y'.num)
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact IntEq_trans
      (intMul_two_by_two_swap x.num y.num (ratDenInt x') (ratDenInt y'))
      (IntEq_trans
        (intMul_right_congr hxInt)
        (IntEq_trans
          (intMul_left_congr hyInt)
          (intMul_two_by_two_swap x'.num (ratDenInt x) y'.num (ratDenInt y))))
  exact IntEq_trans leftToStructured
    (IntEq_trans structured (IntEq_symm rightToStructured))

theorem ratMul_comm (x y : RatNum) :
    RatEq (ratMul x y) (ratMul y x) := by
  unfold RatEq
  change IntEq
    (IntMul (IntMul x.num y.num) (ratDenInt (ratMul y x)))
    (IntMul (IntMul y.num x.num) (ratDenInt (ratMul x y)))
  have denLeft :
      IntEq (ratDenInt (ratMul y x))
        (IntMul (ratDenInt y) (ratDenInt x)) :=
    ratDenInt_mul y x
  have denRight :
      IntEq (ratDenInt (ratMul x y))
        (IntMul (ratDenInt x) (ratDenInt y)) :=
    ratDenInt_mul x y
  have leftToStructured :
      IntEq
        (IntMul (IntMul x.num y.num) (ratDenInt (ratMul y x)))
        (IntMul (IntMul x.num y.num)
          (IntMul (ratDenInt y) (ratDenInt x))) :=
    intMul_left_congr denLeft
  have rightToStructured :
      IntEq
        (IntMul (IntMul y.num x.num) (ratDenInt (ratMul x y)))
        (IntMul (IntMul y.num x.num)
          (IntMul (ratDenInt x) (ratDenInt y))) :=
    intMul_left_congr denRight
  have structured :
      IntEq
        (IntMul (IntMul x.num y.num)
          (IntMul (ratDenInt y) (ratDenInt x)))
        (IntMul (IntMul y.num x.num)
          (IntMul (ratDenInt x) (ratDenInt y))) := by
    exact IntEq_trans
      (intMul_right_congr (IntMul_comm x.num y.num))
      (intMul_left_congr (IntMul_comm (ratDenInt y) (ratDenInt x)))
  exact IntEq_trans leftToStructured
    (IntEq_trans structured (IntEq_symm rightToStructured))

theorem ratMul_assoc (x y z : RatNum) :
    RatEq (ratMul (ratMul x y) z) (ratMul x (ratMul y z)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul
    exact intMul_assoc x.num y.num z.num
  · exact IntEq_trans (ratDenInt_mul (ratMul x y) z)
      (IntEq_trans
        (intMul_right_congr (ratDenInt_mul x y))
        (IntEq_trans
          (intMul_assoc (ratDenInt x) (ratDenInt y) (ratDenInt z))
          (IntEq_trans
            (intMul_left_congr (IntEq_symm (ratDenInt_mul y z)))
            (IntEq_symm (ratDenInt_mul x (ratMul y z))))))

theorem ratOne_mul_left (x : RatNum) :
    RatEq (ratMul ratOne x) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratOne intToRat
    exact intMul_one_left x.num
  · exact IntEq_trans (ratDenInt_mul ratOne x)
      (IntEq_trans
        (intMul_right_congr ratDenInt_one)
        (intMul_one_left (ratDenInt x)))

theorem ratMul_one_right (x : RatNum) :
    RatEq (ratMul x ratOne) x := by
  exact RatEq_trans (ratMul x ratOne) (ratMul ratOne x) x
    (ratMul_comm x ratOne) (ratOne_mul_left x)

theorem ratMul_respects_left {x x' y : RatNum} :
    RatEq x x' -> RatEq (ratMul x y) (ratMul x' y) := by
  intro hx
  exact ratMul_respects hx (RatEq_refl y)

theorem ratMul_respects_right {x y y' : RatNum} :
    RatEq y y' -> RatEq (ratMul x y) (ratMul x y') := by
  intro hy
  exact ratMul_respects (RatEq_refl x) hy

structure RatMultiplicativeLaws where
  mul_respects :
    ∀ {x x' y y' : RatNum}, RatEq x x' -> RatEq y y' ->
      RatEq (ratMul x y) (ratMul x' y')
  mul_comm : ∀ x y : RatNum, RatEq (ratMul x y) (ratMul y x)
  rat_eq_trans : ∀ x y z : RatNum, RatEq x y -> RatEq y z -> RatEq x z
  inv_apart_mul : ∀ x : RatNum, ∀ hx : ratApart0 x,
    RatEq (ratMul x (ratInvApart x hx)) ratOne

theorem RatMultiplicative_laws : RatMultiplicativeLaws where
  mul_respects := by
    intro x x' y y' hx hy
    exact ratMul_respects hx hy
  mul_comm := ratMul_comm
  rat_eq_trans := RatEq_trans
  inv_apart_mul := ratInvApart_mul

theorem ratVal_repr_eq_well_defined {p : BHist} {x y : RatNum}
    {j : BHist × BHist} :
    x = y -> ratVal p x j -> ratVal p y j := by
  intro same val
  cases same
  exact val

def ratAbsInfty (x : RatNum) : RatNum :=
  ratMagnitude x

theorem ratAbsInfty_den (x : RatNum) :
    hsame (ratAbsInfty x).den x.den := by
  exact ratMagnitude_den x

theorem ratAbsInfty_num_nonnegative (x : RatNum) :
    (ratAbsInfty x).num.sign = BMark.b0 := by
  exact ratMagnitude_num_nonnegative x

end BEDC.Derived.RationalUp
