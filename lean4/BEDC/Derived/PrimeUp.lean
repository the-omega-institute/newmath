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

end BEDC.Derived.PrimeUp
