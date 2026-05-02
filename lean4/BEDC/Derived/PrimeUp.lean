import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

inductive NatMul (d : BHist) : BHist -> BHist -> Prop where
  | zero (hd : UnaryHistory d) : NatMul d BHist.Empty BHist.Empty
  | succ {q n n' : BHist} : NatMul d q n -> Cont n d n' -> NatMul d (BHist.e1 q) n'

theorem NatMul_functional {d q n m : BHist} :
    UnaryHistory d -> NatMul d q n -> NatMul d q m -> hsame n m := by
  intro _hd left
  induction left generalizing m with
  | zero _hdZero =>
      intro right
      cases right with
      | zero _hdRight =>
          rfl
  | succ leftPrev leftCont ih =>
      intro right
      cases right with
      | succ rightPrev rightCont =>
          have samePrev : hsame _ _ := ih rightPrev
          exact cont_respects_hsame samePrev (hsame_refl d) leftCont rightCont

theorem NatMul_total {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> ∃ n : BHist, UnaryHistory n ∧ NatMul d q n := by
  intro unaryD unaryQ
  induction q with
  | Empty =>
      exact Exists.intro BHist.Empty (And.intro unary_empty (NatMul.zero unaryD))
  | e0 q =>
      cases unaryQ
  | e1 q ih =>
      have totalQ : ∃ n : BHist, UnaryHistory n ∧ NatMul d q n := ih unaryQ
      cases totalQ with
      | intro n nData =>
          exact Exists.intro (append n d)
            (And.intro (unary_append_closed nData.left unaryD)
              (NatMul.succ nData.right (cont_intro rfl)))

def NatDivides (d n : BHist) : Prop :=
  ∃ q : BHist, UnaryHistory q ∧ NatMul d q n

end BEDC.Derived.PrimeUp
