import BEDC.Derived.FactorialUp
import BEDC.Derived.PrimeUp.UnitResult

namespace BEDC.Derived.CatalanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne
abbrev NatThree : BHist := BHist.e1 NatTwo
abbrev NatFour : BHist := BHist.e1 NatThree
abbrev NatFive : BHist := BHist.e1 NatFour

private theorem natOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

private theorem natTwo_unary : UnaryHistory NatTwo :=
  unary_e1_closed natOne_unary

private theorem natThree_unary : UnaryHistory NatThree :=
  unary_e1_closed natTwo_unary

private theorem natOne_mul_self : NatMul NatOne NatOne NatOne :=
  NatMul_unit_left_closed natOne_unary

private theorem natOne_mul_two : NatMul NatOne NatTwo NatTwo :=
  NatMul_unit_left_closed natTwo_unary

private theorem natTwo_mul_one : NatMul NatTwo NatOne NatTwo :=
  NatMul.succ (NatMul.zero natTwo_unary) (cont_left_unit NatTwo)

private theorem natOne_add_one : NatAdd NatOne NatOne NatTwo :=
  NatAdd_append_self natOne_unary natOne_unary

private theorem natOne_add_two : NatAdd NatOne NatTwo NatThree :=
  NatAdd_append_self natOne_unary natTwo_unary

private theorem natTwo_add_three : NatAdd NatTwo NatThree NatFive :=
  NatAdd_append_self natTwo_unary natThree_unary

/-!
  Catalan 递归以有限卷积窗口编码。`CatalanConv left right sum`
  表示从 `left` 起、长度由 `right` 控制的窗口乘积和。
-/
mutual
  inductive Catalan : BHist -> BHist -> Prop where
    | zero : Catalan BHist.Empty NatOne
    | succ {n sum : BHist} :
        CatalanConv BHist.Empty n sum -> Catalan (BHist.e1 n) sum

  inductive CatalanConv : BHist -> BHist -> BHist -> Prop where
    | last {left a b product : BHist} :
        Catalan left a -> Catalan BHist.Empty b -> NatMul a b product ->
          CatalanConv left BHist.Empty product
    | step {left right a b head tail sum : BHist} :
        Catalan left a -> Catalan (BHist.e1 right) b -> NatMul a b head ->
          CatalanConv (BHist.e1 left) right tail -> NatAdd head tail sum ->
            CatalanConv left (BHist.e1 right) sum
end

theorem catalan_zero : Catalan BHist.Empty NatOne :=
  Catalan.zero

theorem catalan_one_convolution : CatalanConv BHist.Empty BHist.Empty NatOne :=
  CatalanConv.last Catalan.zero Catalan.zero natOne_mul_self

theorem catalan_one : Catalan NatOne NatOne :=
  Catalan.succ catalan_one_convolution

theorem catalan_two_convolution : CatalanConv BHist.Empty NatOne NatTwo :=
  CatalanConv.step Catalan.zero catalan_one natOne_mul_self
    (CatalanConv.last catalan_one Catalan.zero natOne_mul_self)
    natOne_add_one

theorem catalan_two : Catalan NatTwo NatTwo :=
  Catalan.succ catalan_two_convolution

theorem catalan_three_middle_convolution : CatalanConv NatOne NatOne NatThree :=
  CatalanConv.step catalan_one catalan_one natOne_mul_self
    (CatalanConv.last catalan_two Catalan.zero natTwo_mul_one)
    natOne_add_two

theorem catalan_three_convolution : CatalanConv BHist.Empty NatTwo NatFive :=
  CatalanConv.step Catalan.zero catalan_two natOne_mul_two
    catalan_three_middle_convolution
    natTwo_add_three

theorem catalan_three : Catalan NatThree NatFive :=
  Catalan.succ catalan_three_convolution

theorem catalan_succ_of_convolution {n sum : BHist} :
    CatalanConv BHist.Empty n sum -> Catalan (BHist.e1 n) sum := by
  intro conv
  exact Catalan.succ conv

theorem catalan_succ_iff_convolution {n sum : BHist} :
    Catalan (BHist.e1 n) sum <-> CatalanConv BHist.Empty n sum := by
  constructor
  · intro cat
    cases cat with
    | succ conv =>
        exact conv
  · intro conv
    exact Catalan.succ conv

theorem catalan_recursion_property :
    (∀ {n sum : BHist}, CatalanConv BHist.Empty n sum ->
      Catalan (BHist.e1 n) sum) ∧
      Catalan BHist.Empty NatOne := by
  constructor
  · intro n sum conv
    exact catalan_succ_of_convolution conv
  · exact Catalan.zero

theorem catalan_small_values :
    Catalan BHist.Empty NatOne ∧ Catalan NatOne NatOne ∧
      Catalan NatTwo NatTwo ∧ Catalan NatThree NatFive := by
  constructor
  · exact catalan_zero
  · constructor
    · exact catalan_one
    · constructor
      · exact catalan_two
      · exact catalan_three

theorem CatalanUp_constructive_export :
    Catalan BHist.Empty NatOne ∧ Catalan NatOne NatOne ∧
      Catalan NatTwo NatTwo ∧ Catalan NatThree NatFive ∧
        (∀ {n sum : BHist}, CatalanConv BHist.Empty n sum ->
          Catalan (BHist.e1 n) sum) := by
  constructor
  · exact catalan_zero
  · constructor
    · exact catalan_one
    · constructor
      · exact catalan_two
      · constructor
        · exact catalan_three
        · intro n sum conv
          exact catalan_succ_of_convolution conv

end BEDC.Derived.CatalanUp
