import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.NatUp.UnaryNatBridge

/-
BEDC unary 乘法关系 NatMulRel 经重复 NatAdd grounded，桥到 Lean Nat 乘法。
与 UnaryNatBridge 一起使 UnaryHistory ≃ Lean Nat 成为 +/*/≤ 全保结构的有序半环桥；mathlib-free，0-axiom。
-/

namespace BEDC.Derived.NatUp.UnaryNatMulBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.NatUp.UnaryNatBridge

inductive NatMulRel : BHist → BHist → BHist → Prop where
  | zero (m : BHist) : UnaryHistory m → NatMulRel m BHist.Empty BHist.Empty
  | succ (m n p q : BHist) : NatMulRel m n q → NatAdd m q p → NatMulRel m (BHist.e1 n) p

theorem unaryLength_natMul {m n p : BHist} (h : NatMulRel m n p) :
    unaryLength p = unaryLength m * unaryLength n := by
  induction h with
  | zero _ =>
      exact (Nat.mul_zero (unaryLength m)).symm
  | succ n p q _ hadd ih =>
      have hp : unaryLength p = unaryLength m + unaryLength q :=
        unaryLength_natAdd hadd
      have hsum :
          unaryLength m + unaryLength q =
            unaryLength m * unaryLength (BHist.e1 n) := by
        exact (congrArg (fun x => unaryLength m + x) ih).trans
          ((Nat.add_comm (unaryLength m) (unaryLength m * unaryLength n)).trans
            (Nat.mul_succ (unaryLength m) (unaryLength n)).symm)
      exact hp.trans hsum

end BEDC.Derived.NatUp.UnaryNatMulBridge
