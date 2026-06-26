import BEDC.Derived.CatalanUp
import BEDC.Derived.MotzkinUp
import BEDC.Derived.PrimeUp.UnitResult

namespace BEDC.Derived.SchroderUp

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
abbrev NatTwentyTwo : BHist := BHist.e1 NatTwentyOne

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

private theorem natSix_unary : UnaryHistory NatSix :=
  unary_e1_closed natFive_unary

private theorem natTen_unary : UnaryHistory NatTen :=
  unary_e1_closed
    (unary_e1_closed
      (unary_e1_closed
        (unary_e1_closed natSix_unary)))

private theorem natEleven_unary : UnaryHistory NatEleven :=
  unary_e1_closed natTen_unary

private theorem natSixteen_unary : UnaryHistory NatSixteen :=
  unary_e1_closed
    (unary_e1_closed
      (unary_e1_closed
        (unary_e1_closed
          (unary_e1_closed natEleven_unary))))

private theorem natOne_mul_one : NatMul NatOne NatOne NatOne :=
  NatMul_unit_left_closed natOne_unary

private theorem natOne_mul_two : NatMul NatOne NatTwo NatTwo :=
  NatMul_unit_left_closed natTwo_unary

private theorem natOne_mul_six : NatMul NatOne NatSix NatSix :=
  NatMul_unit_left_closed natSix_unary

private theorem natTwo_mul_one : NatMul NatTwo NatOne NatTwo :=
  NatMul.succ (NatMul.zero natTwo_unary) (cont_left_unit NatTwo)

private theorem natTwo_mul_two : NatMul NatTwo NatTwo NatFour :=
  NatMul.succ natTwo_mul_one (cont_intro rfl)

private theorem natSix_mul_one : NatMul NatSix NatOne NatSix :=
  NatMul.succ (NatMul.zero natSix_unary) (cont_left_unit NatSix)

private theorem natOne_add_one : NatAdd NatOne NatOne NatTwo :=
  NatAdd_append_self natOne_unary natOne_unary

private theorem natOne_add_two : NatAdd NatOne NatTwo NatThree :=
  NatAdd_append_self natOne_unary natTwo_unary

private theorem natTwo_add_two : NatAdd NatTwo NatTwo NatFour :=
  NatAdd_append_self natTwo_unary natTwo_unary

private theorem natTwo_add_four : NatAdd NatTwo NatFour NatSix :=
  NatAdd_append_self natTwo_unary natFour_unary

private theorem natFour_add_six : NatAdd NatFour NatSix NatTen :=
  NatAdd_append_self natFour_unary natSix_unary

private theorem natSix_add_four : NatAdd NatSix NatFour NatTen :=
  NatAdd_append_self natSix_unary natFour_unary

private theorem natSix_add_ten : NatAdd NatSix NatTen NatSixteen :=
  NatAdd_append_self natSix_unary natTen_unary

private theorem natTen_add_six : NatAdd NatTen NatSix NatSixteen :=
  NatAdd_append_self natTen_unary natSix_unary

private theorem natSix_add_sixteen : NatAdd NatSix NatSixteen NatTwentyTwo :=
  NatAdd_append_self natSix_unary natSixteen_unary

private theorem natThree_add_three : NatAdd NatThree NatThree NatSix :=
  NatAdd_append_self natThree_unary natThree_unary

private theorem natEleven_add_eleven : NatAdd NatEleven NatEleven NatTwentyTwo :=
  NatAdd_append_self natEleven_unary natEleven_unary

/-!
  大 Schröder 递归按 unary 窗口闭生成：
  `LargeSchroder (n + 1)` 是 `LargeSchroder n` 加上
  `sum_{k=0}^{n} LargeSchroder k * LargeSchroder (n-k)`。
-/
mutual
  inductive LargeSchroder : BHist -> BHist -> Prop where
    | zero : LargeSchroder BHist.Empty NatOne
    | succ {n previous conv sum : BHist} :
        LargeSchroder n previous -> LargeSchroderConv BHist.Empty n conv ->
          NatAdd previous conv sum -> LargeSchroder (BHist.e1 n) sum

  inductive LargeSchroderConv : BHist -> BHist -> BHist -> Prop where
    | last {left a b product : BHist} :
        LargeSchroder left a -> LargeSchroder BHist.Empty b -> NatMul a b product ->
          LargeSchroderConv left BHist.Empty product
    | step {left right a b head tail sum : BHist} :
        LargeSchroder left a -> LargeSchroder (BHist.e1 right) b ->
          NatMul a b head -> LargeSchroderConv (BHist.e1 left) right tail ->
            NatAdd head tail sum -> LargeSchroderConv left (BHist.e1 right) sum
end

inductive SmallSchroder : BHist -> BHist -> Prop where
  | zero : SmallSchroder BHist.Empty NatOne
  | positive {n small large : BHist} :
      LargeSchroder (BHist.e1 n) large -> NatAdd small small large ->
        SmallSchroder (BHist.e1 n) small

theorem large_schroder_zero : LargeSchroder BHist.Empty NatOne :=
  LargeSchroder.zero

theorem large_schroder_one_convolution :
    LargeSchroderConv BHist.Empty BHist.Empty NatOne :=
  LargeSchroderConv.last large_schroder_zero large_schroder_zero natOne_mul_one

theorem large_schroder_one : LargeSchroder NatOne NatTwo :=
  LargeSchroder.succ large_schroder_zero large_schroder_one_convolution
    natOne_add_one

theorem large_schroder_two_convolution :
    LargeSchroderConv BHist.Empty NatOne NatFour :=
  LargeSchroderConv.step large_schroder_zero large_schroder_one natOne_mul_two
    (LargeSchroderConv.last large_schroder_one large_schroder_zero natTwo_mul_one)
    natTwo_add_two

theorem large_schroder_two : LargeSchroder NatTwo NatSix :=
  LargeSchroder.succ large_schroder_one large_schroder_two_convolution
    natTwo_add_four

theorem large_schroder_three_middle_convolution :
    LargeSchroderConv NatOne NatOne NatTen :=
  LargeSchroderConv.step large_schroder_one large_schroder_one natTwo_mul_two
    (LargeSchroderConv.last large_schroder_two large_schroder_zero natSix_mul_one)
    natFour_add_six

theorem large_schroder_three_convolution :
    LargeSchroderConv BHist.Empty NatTwo NatSixteen :=
  LargeSchroderConv.step large_schroder_zero large_schroder_two natOne_mul_six
    large_schroder_three_middle_convolution
    natSix_add_ten

theorem large_schroder_three : LargeSchroder NatThree NatTwentyTwo :=
  LargeSchroder.succ large_schroder_two large_schroder_three_convolution
    natSix_add_sixteen

theorem small_schroder_zero : SmallSchroder BHist.Empty NatOne :=
  SmallSchroder.zero

theorem small_schroder_one : SmallSchroder NatOne NatOne :=
  SmallSchroder.positive large_schroder_one natOne_add_one

theorem small_schroder_two : SmallSchroder NatTwo NatThree :=
  SmallSchroder.positive large_schroder_two natThree_add_three

theorem small_schroder_three : SmallSchroder NatThree NatEleven :=
  SmallSchroder.positive large_schroder_three natEleven_add_eleven

theorem large_schroder_succ_of_convolution {n previous conv sum : BHist} :
    LargeSchroder n previous -> LargeSchroderConv BHist.Empty n conv ->
      NatAdd previous conv sum -> LargeSchroder (BHist.e1 n) sum := by
  intro previousValue convValue addValue
  exact LargeSchroder.succ previousValue convValue addValue

theorem large_schroder_succ_iff_convolution {n sum : BHist} :
    LargeSchroder (BHist.e1 n) sum <->
      ∃ previous : BHist, ∃ conv : BHist,
        LargeSchroder n previous ∧ LargeSchroderConv BHist.Empty n conv ∧
          NatAdd previous conv sum := by
  constructor
  · intro schroder
    cases schroder with
    | succ previousValue convValue addValue =>
        exact ⟨_, _, previousValue, convValue, addValue⟩
  · intro data
    cases data with
    | intro previous rest =>
        cases rest with
        | intro conv payload =>
            exact LargeSchroder.succ payload.left payload.right.left payload.right.right

theorem small_schroder_positive_halves_large {n small : BHist} :
    SmallSchroder (BHist.e1 n) small ->
      ∃ large : BHist, LargeSchroder (BHist.e1 n) large ∧
        NatAdd small small large := by
  intro smallValue
  cases smallValue with
  | positive largeValue doubleValue =>
      exact ⟨_, largeValue, doubleValue⟩

theorem schroder_catalan_initial_bridge :
    LargeSchroder BHist.Empty NatOne ∧
      BEDC.Derived.CatalanUp.Catalan BHist.Empty NatOne ∧
      LargeSchroder NatOne NatTwo ∧
      BEDC.Derived.CatalanUp.Catalan BEDC.Derived.CatalanUp.NatTwo
        BEDC.Derived.CatalanUp.NatTwo := by
  constructor
  · exact large_schroder_zero
  · constructor
    · exact BEDC.Derived.CatalanUp.catalan_zero
    · constructor
      · exact large_schroder_one
      · exact BEDC.Derived.CatalanUp.catalan_two

theorem schroder_motzkin_initial_bridge :
    LargeSchroder BHist.Empty NatOne ∧
      BEDC.Derived.MotzkinUp.Motzkin BHist.Empty NatOne ∧
      LargeSchroder NatOne NatTwo ∧
      BEDC.Derived.MotzkinUp.Motzkin BEDC.Derived.MotzkinUp.NatTwo
        BEDC.Derived.MotzkinUp.NatTwo := by
  constructor
  · exact large_schroder_zero
  · constructor
    · exact BEDC.Derived.MotzkinUp.motzkin_zero
    · constructor
      · exact large_schroder_one
      · exact BEDC.Derived.MotzkinUp.motzkin_two

theorem large_schroder_small_values :
    LargeSchroder BHist.Empty NatOne ∧ LargeSchroder NatOne NatTwo ∧
      LargeSchroder NatTwo NatSix ∧ LargeSchroder NatThree NatTwentyTwo := by
  constructor
  · exact large_schroder_zero
  · constructor
    · exact large_schroder_one
    · constructor
      · exact large_schroder_two
      · exact large_schroder_three

theorem small_schroder_small_values :
    SmallSchroder BHist.Empty NatOne ∧ SmallSchroder NatOne NatOne ∧
      SmallSchroder NatTwo NatThree ∧ SmallSchroder NatThree NatEleven := by
  constructor
  · exact small_schroder_zero
  · constructor
    · exact small_schroder_one
    · constructor
      · exact small_schroder_two
      · exact small_schroder_three

theorem LargeSchroderUp_constructive_export :
    LargeSchroder BHist.Empty NatOne ∧ LargeSchroder NatOne NatTwo ∧
      LargeSchroder NatTwo NatSix ∧ LargeSchroder NatThree NatTwentyTwo ∧
        SmallSchroder NatOne NatOne ∧ SmallSchroder NatTwo NatThree ∧
          SmallSchroder NatThree NatEleven ∧
            (∀ {n previous conv sum : BHist},
              LargeSchroder n previous -> LargeSchroderConv BHist.Empty n conv ->
                NatAdd previous conv sum -> LargeSchroder (BHist.e1 n) sum) ∧
            (∀ {n small : BHist}, SmallSchroder (BHist.e1 n) small ->
              ∃ large : BHist, LargeSchroder (BHist.e1 n) large ∧
                NatAdd small small large) ∧
            (LargeSchroder BHist.Empty NatOne ∧
              BEDC.Derived.CatalanUp.Catalan BHist.Empty NatOne) ∧
            (LargeSchroder BHist.Empty NatOne ∧
              BEDC.Derived.MotzkinUp.Motzkin BHist.Empty NatOne) := by
  constructor
  · exact large_schroder_zero
  · constructor
    · exact large_schroder_one
    · constructor
      · exact large_schroder_two
      · constructor
        · exact large_schroder_three
        · constructor
          · exact small_schroder_one
          · constructor
            · exact small_schroder_two
            · constructor
              · exact small_schroder_three
              · constructor
                · intro n previous conv sum previousValue convValue addValue
                  exact large_schroder_succ_of_convolution previousValue convValue addValue
                · constructor
                  · intro n small smallValue
                    exact small_schroder_positive_halves_large smallValue
                  · constructor
                    · constructor
                      · exact large_schroder_zero
                      · exact BEDC.Derived.CatalanUp.catalan_zero
                    · constructor
                      · exact large_schroder_zero
                      · exact BEDC.Derived.MotzkinUp.motzkin_zero

end BEDC.Derived.SchroderUp
