import BEDC.Derived.PrimeUp.NatMulCases
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary

private theorem unary_hsame_of_bwordLength_eq {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro uh
  induction h generalizing k with
  | Empty =>
      intro uk lengthEq
      cases k with
      | Empty =>
          rfl
      | e0 k =>
          cases uk
      | e1 k =>
          cases lengthEq
  | e0 h _ih =>
      cases uh
  | e1 h ih =>
      intro uk lengthEq
      cases k with
      | Empty =>
          cases lengthEq
      | e0 k =>
          cases uk
      | e1 k =>
          exact hsame_e1_congr (ih uh uk (Nat.succ.inj lengthEq))

theorem NatMul_bwordLength {d q n : BHist} :
    NatMul d q n -> bwordLength n = bwordLength d * bwordLength q := by
  intro mul
  induction mul with
  | zero _hd =>
      exact (Nat.mul_zero (bwordLength d)).symm
  | succ previous step ih =>
      calc
        bwordLength _ = bwordLength (BEDC.FKernel.Cont.append _ d) := congrArg bwordLength step
        _ = bwordLength _ + bwordLength d := bwordLength_append _ d
        _ = bwordLength d * bwordLength _ + bwordLength d :=
          congrArg (fun x => x + bwordLength d) ih
        _ = bwordLength d * Nat.succ (bwordLength _) :=
          (Nat.mul_succ (bwordLength d) (bwordLength _)).symm

theorem NatMul_comm_hsame {d q n m : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d q n -> NatMul q d m -> hsame n m := by
  intro hd hq left right
  have unaryN : UnaryHistory n := NatMul_result_unary hd left
  have unaryM : UnaryHistory m := NatMul_result_unary hq right
  apply unary_hsame_of_bwordLength_eq unaryN unaryM
  calc
    bwordLength n = bwordLength d * bwordLength q := NatMul_bwordLength left
    _ = bwordLength q * bwordLength d := Nat.mul_comm (bwordLength d) (bwordLength q)
    _ = bwordLength m := (NatMul_bwordLength right).symm

end BEDC.Derived.PrimeUp
