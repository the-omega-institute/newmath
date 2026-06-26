import BEDC.Derived.CatalanUp
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.UnitResult

namespace BEDC.Derived.MotzkinUp

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
abbrev NatSix : BHist := BHist.e1 NatFive
abbrev NatSeven : BHist := BHist.e1 NatSix
abbrev NatEight : BHist := BHist.e1 NatSeven
abbrev NatNine : BHist := BHist.e1 NatEight
abbrev NatTen : BHist := BHist.e1 NatNine
abbrev NatEleven : BHist := BHist.e1 NatTen
abbrev NatTwelve : BHist := BHist.e1 NatEleven
abbrev NatThirteen : BHist := BHist.e1 NatTwelve
abbrev NatFourteen : BHist := BHist.e1 NatThirteen
abbrev NatFifteen : BHist := BHist.e1 NatFourteen
abbrev NatSixteen : BHist := BHist.e1 NatFifteen
abbrev NatSeventeen : BHist := BHist.e1 NatSixteen
abbrev NatEighteen : BHist := BHist.e1 NatSeventeen
abbrev NatNineteen : BHist := BHist.e1 NatEighteen
abbrev NatTwenty : BHist := BHist.e1 NatNineteen
abbrev NatTwentyOne : BHist := BHist.e1 NatTwenty

private theorem natOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

private theorem natTwo_unary : UnaryHistory NatTwo :=
  unary_e1_closed natOne_unary

private theorem natThree_unary : UnaryHistory NatThree :=
  unary_e1_closed natTwo_unary

private theorem natFour_unary : UnaryHistory NatFour :=
  unary_e1_closed natThree_unary

private theorem natFive_unary : UnaryHistory NatFive :=
  unary_e1_closed natFour_unary

private theorem natNine_unary : UnaryHistory NatNine :=
  unary_e1_closed
    (unary_e1_closed
      (unary_e1_closed
        (unary_e1_closed natFive_unary)))

private theorem natTwelve_unary : UnaryHistory NatTwelve :=
  unary_e1_closed
    (unary_e1_closed
      (unary_e1_closed natNine_unary))

private theorem natOne_mul_one : NatMul NatOne NatOne NatOne :=
  NatMul_unit_left_closed natOne_unary

private theorem natOne_mul_two : NatMul NatOne NatTwo NatTwo :=
  NatMul_unit_left_closed natTwo_unary

private theorem natOne_mul_four : NatMul NatOne NatFour NatFour :=
  NatMul_unit_left_closed natFour_unary

private theorem natTwo_mul_one : NatMul NatTwo NatOne NatTwo :=
  NatMul.succ (NatMul.zero natTwo_unary) (cont_left_unit NatTwo)

private theorem natTwo_mul_two : NatMul NatTwo NatTwo NatFour :=
  NatMul.succ natTwo_mul_one (cont_intro rfl)

private theorem natFour_mul_one : NatMul NatFour NatOne NatFour :=
  NatMul.succ (NatMul.zero natFour_unary) (cont_left_unit NatFour)

private theorem natOne_add_empty : NatAdd NatOne BHist.Empty NatOne :=
  NatAdd_append_self natOne_unary unary_empty

private theorem natOne_add_one : NatAdd NatOne NatOne NatTwo :=
  NatAdd_append_self natOne_unary natOne_unary

private theorem natTwo_add_empty : NatAdd NatTwo BHist.Empty NatTwo :=
  NatAdd_append_self natTwo_unary unary_empty

private theorem natFour_add_empty : NatAdd NatFour BHist.Empty NatFour :=
  NatAdd_append_self natFour_unary unary_empty

private theorem natTwo_add_two : NatAdd NatTwo NatTwo NatFour :=
  NatAdd_append_self natTwo_unary natTwo_unary

private theorem natOne_add_two : NatAdd NatOne NatTwo NatThree :=
  NatAdd_append_self natOne_unary natTwo_unary

private theorem natFour_add_five : NatAdd NatFour NatFive NatNine :=
  NatAdd_append_self natFour_unary natFive_unary

private theorem natFour_add_two : NatAdd NatFour NatTwo NatSix :=
  NatAdd_append_self natFour_unary natTwo_unary

private theorem natTwo_add_one : NatAdd NatTwo NatOne NatThree :=
  NatAdd_append_self natTwo_unary natOne_unary

private theorem natTwo_add_three : NatAdd NatTwo NatThree NatFive :=
  NatAdd_append_self natTwo_unary natThree_unary

private theorem natTwo_add_four : NatAdd NatTwo NatFour NatSix :=
  NatAdd_append_self natTwo_unary natFour_unary

private theorem natThree_add_two : NatAdd NatThree NatTwo NatFive :=
  NatAdd_append_self natThree_unary natTwo_unary

private theorem natTwo_add_six : NatAdd NatTwo NatSix NatEight :=
  NatAdd_append_self natTwo_unary (unary_e1_closed natFive_unary)

private theorem natFour_add_eight : NatAdd NatFour NatEight NatTwelve :=
  NatAdd_append_self natFour_unary
    (unary_e1_closed (unary_e1_closed (unary_e1_closed natFive_unary)))

private theorem natNine_add_twelve : NatAdd NatNine NatTwelve NatTwentyOne :=
  NatAdd_append_self natNine_unary natTwelve_unary

/-!
  卷积窗口 `MotzkinConv left count sum` 读取 `count` 个连续乘积,
  从 `M_left * M_(count - 1)` 开始; 空窗口给出零和项.
-/
mutual
  inductive Motzkin : BHist -> BHist -> Prop where
    | zero : Motzkin BHist.Empty NatOne
    | succ {n current conv next : BHist} :
        Motzkin n current -> MotzkinConv BHist.Empty n conv ->
          NatAdd current conv next -> Motzkin (BHist.e1 n) next

  inductive MotzkinConv : BHist -> BHist -> BHist -> Prop where
    | empty {left : BHist} :
        MotzkinConv left BHist.Empty BHist.Empty
    | step {left right a b head tail sum : BHist} :
        Motzkin left a -> Motzkin right b -> NatMul a b head ->
          MotzkinConv (BHist.e1 left) right tail -> NatAdd head tail sum ->
            MotzkinConv left (BHist.e1 right) sum
end

theorem motzkin_zero : Motzkin BHist.Empty NatOne :=
  Motzkin.zero

theorem motzkin_one_convolution : MotzkinConv BHist.Empty BHist.Empty BHist.Empty :=
  MotzkinConv.empty

theorem motzkin_one : Motzkin NatOne NatOne :=
  Motzkin.succ motzkin_zero motzkin_one_convolution natOne_add_empty

theorem motzkin_two_convolution : MotzkinConv BHist.Empty NatOne NatOne :=
  MotzkinConv.step motzkin_zero motzkin_zero natOne_mul_one
    MotzkinConv.empty natOne_add_empty

theorem motzkin_two : Motzkin NatTwo NatTwo :=
  Motzkin.succ motzkin_one motzkin_two_convolution natOne_add_one

theorem motzkin_three_convolution : MotzkinConv BHist.Empty NatTwo NatTwo :=
  MotzkinConv.step motzkin_zero motzkin_one natOne_mul_one
    (MotzkinConv.step motzkin_one motzkin_zero natOne_mul_one
      MotzkinConv.empty natOne_add_empty)
    natOne_add_one

theorem motzkin_three : Motzkin NatThree NatFour :=
  Motzkin.succ motzkin_two motzkin_three_convolution natTwo_add_two

theorem motzkin_four_convolution : MotzkinConv BHist.Empty NatThree NatFive :=
  MotzkinConv.step motzkin_zero motzkin_two natOne_mul_two
    (MotzkinConv.step motzkin_one motzkin_one natOne_mul_one
      (MotzkinConv.step motzkin_two motzkin_zero natTwo_mul_one
        MotzkinConv.empty natTwo_add_empty)
      natOne_add_two)
    natTwo_add_three

theorem motzkin_four : Motzkin NatFour NatNine :=
  Motzkin.succ motzkin_three motzkin_four_convolution natFour_add_five

theorem motzkin_five_convolution : MotzkinConv BHist.Empty NatFour NatTwelve :=
  MotzkinConv.step motzkin_zero motzkin_three natOne_mul_four
    (MotzkinConv.step motzkin_one motzkin_two natOne_mul_two
      (MotzkinConv.step motzkin_two motzkin_one natTwo_mul_one
        (MotzkinConv.step motzkin_three motzkin_zero natFour_mul_one
          MotzkinConv.empty natFour_add_empty)
        natTwo_add_four)
      natTwo_add_six)
    natFour_add_eight

theorem motzkin_five : Motzkin NatFive NatTwentyOne :=
  Motzkin.succ motzkin_four motzkin_five_convolution natNine_add_twelve

theorem motzkin_succ_of_convolution {n current conv next : BHist} :
    Motzkin n current -> MotzkinConv BHist.Empty n conv ->
      NatAdd current conv next -> Motzkin (BHist.e1 n) next := by
  intro currentValue convValue addValue
  exact Motzkin.succ currentValue convValue addValue

theorem motzkin_succ_iff_convolution {n next : BHist} :
    Motzkin (BHist.e1 n) next <->
      ∃ current : BHist, ∃ conv : BHist,
        Motzkin n current ∧ MotzkinConv BHist.Empty n conv ∧
          NatAdd current conv next := by
  constructor
  · intro motzkin
    cases motzkin with
    | succ currentValue convValue addValue =>
        exact ⟨_, _, currentValue, convValue, addValue⟩
  · intro data
    cases data with
    | intro current rest =>
        cases rest with
        | intro conv payload =>
            exact Motzkin.succ payload.left payload.right.left payload.right.right

theorem motzkin_catalan_initial_bridge :
    Motzkin BHist.Empty NatOne ∧
      BEDC.Derived.CatalanUp.Catalan BHist.Empty NatOne := by
  constructor
  · exact motzkin_zero
  · exact BEDC.Derived.CatalanUp.catalan_zero

theorem motzkin_small_values :
    Motzkin BHist.Empty NatOne ∧ Motzkin NatOne NatOne ∧
      Motzkin NatTwo NatTwo ∧ Motzkin NatThree NatFour ∧
        Motzkin NatFour NatNine ∧ Motzkin NatFive NatTwentyOne := by
  constructor
  · exact motzkin_zero
  · constructor
    · exact motzkin_one
    · constructor
      · exact motzkin_two
      · constructor
        · exact motzkin_three
        · constructor
          · exact motzkin_four
          · exact motzkin_five

theorem MotzkinUp_constructive_export :
    Motzkin BHist.Empty NatOne ∧ Motzkin NatOne NatOne ∧
      Motzkin NatTwo NatTwo ∧ Motzkin NatThree NatFour ∧
        Motzkin NatFour NatNine ∧ Motzkin NatFive NatTwentyOne ∧
          (∀ {n current conv next : BHist},
            Motzkin n current -> MotzkinConv BHist.Empty n conv ->
              NatAdd current conv next -> Motzkin (BHist.e1 n) next) ∧
          (Motzkin BHist.Empty NatOne ∧
            BEDC.Derived.CatalanUp.Catalan BHist.Empty NatOne) := by
  constructor
  · exact motzkin_zero
  · constructor
    · exact motzkin_one
    · constructor
      · exact motzkin_two
      · constructor
        · exact motzkin_three
        · constructor
          · exact motzkin_four
          · constructor
            · exact motzkin_five
            · constructor
              · intro n current conv next currentValue convValue addValue
                exact motzkin_succ_of_convolution currentValue convValue addValue
              · exact motzkin_catalan_initial_bridge

end BEDC.Derived.MotzkinUp
