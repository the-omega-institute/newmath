import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

/-!
# Nonabelian carry certificate for the scalar RP boundary

This file records a concrete Pauli/Heisenberg carry witness.  The scalar
self-substitution reflection-positivity no-go is sharp in this limited sense:
a matrix lift can have nontrivial commutator holonomy while its displayed
finite Gram window is a square-sum PSD certificate.

Scope: this is a concrete nonabelian matrix/CP-lift witness.  It does not
assert a spectral statement about GNS data, and it is not RH evidence.
-/

namespace BEDC.Derived.Visions

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel

structure PauliXM2 where
  a11 : Int
  a12 : Int
  a21 : Int
  a22 : Int
deriving DecidableEq

def pauliXMul (A B : PauliXM2) : PauliXM2 :=
  { a11 := A.a11 * B.a11 + A.a12 * B.a21
    a12 := A.a11 * B.a12 + A.a12 * B.a22
    a21 := A.a21 * B.a11 + A.a22 * B.a21
    a22 := A.a21 * B.a12 + A.a22 * B.a22 }

def pauliXNeg (A : PauliXM2) : PauliXM2 :=
  { a11 := -A.a11
    a12 := -A.a12
    a21 := -A.a21
    a22 := -A.a22 }

def pauliXTranspose (A : PauliXM2) : PauliXM2 :=
  { a11 := A.a11
    a12 := A.a21
    a21 := A.a12
    a22 := A.a22 }

def pauliXId : PauliXM2 :=
  { a11 := 1, a12 := 0, a21 := 0, a22 := 1 }

def pauliXU : PauliXM2 :=
  { a11 := 1, a12 := 0, a21 := 0, a22 := -1 }

def pauliXV : PauliXM2 :=
  { a11 := 0, a12 := 1, a21 := 1, a22 := 0 }

def pauliXUV : PauliXM2 :=
  pauliXMul pauliXU pauliXV

def pauliXCommutator : PauliXM2 :=
  pauliXMul (pauliXMul (pauliXMul pauliXU pauliXV) pauliXU) pauliXV

def pauliXTrace (A : PauliXM2) : Int :=
  A.a11 + A.a22

theorem nonabelian_commutator_eq_neg_id :
    pauliXCommutator = pauliXNeg pauliXId := by
  decide

theorem nonabelian_uv_eq_rotation :
    pauliXUV = { a11 := 0, a12 := 1, a21 := -1, a22 := 0 } := by
  decide

theorem nonabelian_u_square_eq_id :
    pauliXMul pauliXU pauliXU = pauliXId := by
  decide

theorem nonabelian_v_square_eq_id :
    pauliXMul pauliXV pauliXV = pauliXId := by
  decide

theorem nonabelian_holonomy_trace_eq_neg_two :
    pauliXTrace pauliXCommutator = -2 := by
  decide

theorem nonabelian_holonomy_nontrivial :
    pauliXTrace pauliXCommutator ≠ 2 := by
  decide

def pauliXPath (i : Bool) : PauliXM2 :=
  if i then pauliXV else pauliXU

def pauliXGramEntry (i j : Bool) : PauliXM2 :=
  pauliXMul (pauliXTranspose (pauliXPath i)) (pauliXPath j)

def pauliXGram4 : List (List Int) :=
  [[1, 0, 0, 1],
   [0, 1, -1, 0],
   [0, -1, 1, 0],
   [1, 0, 0, 1]]

theorem nonabelian_full_window_gram_from_uv_paths :
    pauliXGram4 =
      [[(pauliXGramEntry false false).a11, (pauliXGramEntry false false).a12,
        (pauliXGramEntry false true).a11, (pauliXGramEntry false true).a12],
       [(pauliXGramEntry false false).a21, (pauliXGramEntry false false).a22,
        (pauliXGramEntry false true).a21, (pauliXGramEntry false true).a22],
       [(pauliXGramEntry true false).a11, (pauliXGramEntry true false).a12,
        (pauliXGramEntry true true).a11, (pauliXGramEntry true true).a12],
       [(pauliXGramEntry true false).a21, (pauliXGramEntry true false).a22,
        (pauliXGramEntry true true).a21, (pauliXGramEntry true true).a22]] := by
  decide

def pauliXExpandedPairQuad (x y : RatNum) : RatNum :=
  ratAdd
    (ratAdd (ratMul x x) (ratNeg (ratMul x y)))
    (ratAdd (ratNeg (ratMul y x)) (ratMul y y))

def pauliXExpandedAddPairQuad (x y : RatNum) : RatNum :=
  ratAdd
    (ratAdd (ratMul x x) (ratMul x y))
    (ratAdd (ratMul y x) (ratMul y y))

def pauliXGramQuad (a b c d : RatNum) : RatNum :=
  ratAdd (pauliXExpandedAddPairQuad a d) (pauliXExpandedPairQuad b c)

def pauliXSosQuad (a b c d : RatNum) : RatNum :=
  ratAdd
    (ratMul (ratAdd a d) (ratAdd a d))
    (ratMul (ratSub b c) (ratSub b c))

private theorem pauliX_ratNum_zero_to_RatEq_zero {x : RatNum} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem pauliX_ratMul_zero_left (x : RatNum) :
    RatEq (ratMul ratZero x) ratZero := by
  apply pauliX_ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem pauliX_ratMul_neg_right (x y : RatNum) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem pauliX_ratMul_neg_left (x y : RatNum) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (pauliX_ratMul_neg_right y x)
      (ratNeg_respects (ratMul_comm y x)))

private theorem pauliX_ratSub_mul_left (x y z : RatNum) :
    RatEq (ratMul (ratSub x y) z)
      (ratAdd (ratMul x z) (ratNeg (ratMul y z))) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratMul_add_right x (ratNeg y) z)
    (ratAdd_respects
      (RatEq_refl (ratMul x z))
      (pauliX_ratMul_neg_left y z))

private theorem pauliX_ratSub_mul_right (x y z : RatNum) :
    RatEq (ratMul x (ratSub y z))
      (ratAdd (ratMul x y) (ratNeg (ratMul x z))) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratMul_add_left x y (ratNeg z))
    (ratAdd_respects
      (RatEq_refl (ratMul x y))
      (pauliX_ratMul_neg_right x z))

private theorem pauliX_ratSub_square_expand (x y : RatNum) :
    RatEq (ratMul (ratSub x y) (ratSub x y))
      (ratAdd
        (ratAdd (ratMul x x) (ratNeg (ratMul x y)))
        (ratAdd (ratNeg (ratMul y x)) (ratMul y y))) := by
  have first :
      RatEq (ratMul (ratSub x y) (ratSub x y))
        (ratAdd
          (ratMul x (ratSub x y))
          (ratNeg (ratMul y (ratSub x y)))) :=
    pauliX_ratSub_mul_left x y (ratSub x y)
  have xTerm :
      RatEq (ratMul x (ratSub x y))
        (ratAdd (ratMul x x) (ratNeg (ratMul x y))) :=
    pauliX_ratSub_mul_right x x y
  have yTermRaw :
      RatEq (ratMul y (ratSub x y))
        (ratAdd (ratMul y x) (ratNeg (ratMul y y))) :=
    pauliX_ratSub_mul_right y x y
  have yTerm :
      RatEq (ratNeg (ratMul y (ratSub x y)))
        (ratAdd (ratNeg (ratMul y x)) (ratMul y y)) := by
    exact RatEq_trans _ _ _
      (ratNeg_respects yTermRaw)
      (RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratNeg_add_dist_local
          (ratMul y x) (ratNeg (ratMul y y)))
        (ratAdd_respects
          (RatEq_refl (ratNeg (ratMul y x)))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul y y))))
  exact RatEq_trans _ _ _ first (ratAdd_respects xTerm yTerm)

private theorem pauliX_ratAdd_square_expand (x y : RatNum) :
    RatEq (ratMul (ratAdd x y) (ratAdd x y))
      (ratAdd
        (ratAdd (ratMul x x) (ratMul x y))
        (ratAdd (ratMul y x) (ratMul y y))) := by
  have first :
      RatEq (ratMul (ratAdd x y) (ratAdd x y))
        (ratAdd
          (ratMul x (ratAdd x y))
          (ratMul y (ratAdd x y))) :=
    ratMul_add_right x y (ratAdd x y)
  have xTerm :
      RatEq (ratMul x (ratAdd x y))
        (ratAdd (ratMul x x) (ratMul x y)) :=
    ratMul_add_left x x y
  have yTerm :
      RatEq (ratMul y (ratAdd x y))
        (ratAdd (ratMul y x) (ratMul y y)) :=
    ratMul_add_left y x y
  exact RatEq_trans _ _ _ first (ratAdd_respects xTerm yTerm)

private theorem pauliX_ratAdd_nonneg {x y : RatNum}
    (hx : ratLe ratZero x) (hy : ratLe ratZero y) :
    ratLe ratZero (ratAdd x y) := by
  have raw : ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

private theorem pauliX_ratMul_self_nonneg (x : RatNum) :
    ratLe ratZero (ratMul x x) := by
  apply ratNonneg_of_num
  have squareNum :
      IntEq (ratMul x x).num
        (intOfNat (natMulFn x.num.magnitude x.num.magnitude)
          (natMulFn_unary x.num.carrier.right x.num.carrier.right)) := by
    change IntEq (IntMul x.num x.num)
      (intOfNat (natMulFn x.num.magnitude x.num.magnitude)
        (natMulFn_unary x.num.carrier.right x.num.carrier.right))
    exact intMul_same_sign_nat x.num.sign x.num.magnitude x.num.magnitude
      x.num.carrier.right x.num.carrier.right
  exact intLe_respects (IntEq_refl intZero) (IntEq_symm squareNum)
    (intLe_zero_of_nat (natMulFn x.num.magnitude x.num.magnitude)
      (natMulFn_unary x.num.carrier.right x.num.carrier.right))

theorem nonabelian_full_window_quad_eq_sos
    (a b c d : RatNum) :
    RatEq (pauliXGramQuad a b c d) (pauliXSosQuad a b c d) := by
  unfold pauliXGramQuad pauliXSosQuad
  unfold pauliXExpandedAddPairQuad pauliXExpandedPairQuad
  exact RatEq_symm
    (ratAdd_respects
      (pauliX_ratAdd_square_expand a d)
      (pauliX_ratSub_square_expand b c))

theorem nonabelian_full_window_psd_sos
    (a b c d : RatNum) :
    ratLe ratZero (pauliXSosQuad a b c d) := by
  unfold pauliXSosQuad
  exact pauliX_ratAdd_nonneg
    (pauliX_ratMul_self_nonneg (ratAdd a d))
    (pauliX_ratMul_self_nonneg (ratSub b c))

theorem nonabelian_full_window_psd
    (a b c d : RatNum) :
    ratLe ratZero (pauliXGramQuad a b c d) := by
  exact ratLe_of_RatEq_right
    (nonabelian_full_window_psd_sos a b c d)
    (RatEq_symm (nonabelian_full_window_quad_eq_sos a b c d))

theorem nonabelian_carry_certificate :
    pauliXCommutator = pauliXNeg pauliXId ∧
      pauliXTrace pauliXCommutator = -2 ∧
      pauliXTrace pauliXCommutator ≠ 2 ∧
      pauliXGram4 =
        [[1, 0, 0, 1],
         [0, 1, -1, 0],
         [0, -1, 1, 0],
         [1, 0, 0, 1]] ∧
      (∀ a b c d : RatNum,
        RatEq (pauliXGramQuad a b c d) (pauliXSosQuad a b c d) ∧
          ratLe ratZero (pauliXGramQuad a b c d)) := by
  constructor
  · exact nonabelian_commutator_eq_neg_id
  · constructor
    · exact nonabelian_holonomy_trace_eq_neg_two
    · constructor
      · exact nonabelian_holonomy_nontrivial
      · constructor
        · rfl
        · intro a b c d
          constructor
          · exact nonabelian_full_window_quad_eq_sos a b c d
          · exact nonabelian_full_window_psd a b c d

end BEDC.Derived.Visions
