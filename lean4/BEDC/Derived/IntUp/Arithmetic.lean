import BEDC.Derived.IntUp
import BEDC.Derived.NatUp
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (append bwordLength bwordLength_append)

def natToUnary : Nat -> BHist
  | 0 => BHist.Empty
  | n + 1 => BHist.e1 (natToUnary n)

theorem natToUnary_unary (n : Nat) : UnaryHistory (natToUnary n) := by
  induction n with
  | zero =>
      exact unary_empty
  | succ _ ih =>
      exact unary_e1_closed ih

theorem natToUnary_length (n : Nat) : bwordLength (natToUnary n) = n := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, succLength, _noZero, _sameIff, _contAdd⟩
  induction n with
  | zero =>
      exact emptyLength
  | succ n ih =>
      change bwordLength (BHist.e1 (natToUnary n)) = Nat.succ n
      rw [succLength (natToUnary n) (natToUnary_unary n), ih]

def pairAdd (x y : BHist × BHist) : BHist × BHist :=
  (append x.1 y.1, append x.2 y.2)

def pairNeg (x : BHist × BHist) : BHist × BHist :=
  (x.2, x.1)

def natMulFn (d : BHist) : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 q => append (natMulFn d q) d

theorem natMulFn_unary {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> UnaryHistory (natMulFn d q) := by
  intro hd hq
  induction q with
  | Empty =>
      exact unary_empty
  | e0 _ =>
      cases hq
  | e1 q ih =>
      exact unary_append_closed (ih hq) hd

theorem natMulFn_rel {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> BEDC.Derived.PrimeUp.NatMul d q (natMulFn d q) := by
  intro hd hq
  induction q with
  | Empty =>
      exact BEDC.Derived.PrimeUp.NatMul.zero hd
  | e0 _ =>
      cases hq
  | e1 q ih =>
      exact BEDC.Derived.PrimeUp.NatMul.succ (ih hq) (BEDC.FKernel.Cont.cont_intro rfl)

theorem natMulFn_bwordLength {d q : BHist} :
    UnaryHistory d -> UnaryHistory q ->
      bwordLength (natMulFn d q) = bwordLength d * bwordLength q := by
  intro hd hq
  exact BEDC.Derived.PrimeUp.NatMul_bwordLength (natMulFn_rel hd hq)

def pairMul (x y : BHist × BHist) : BHist × BHist :=
  (append (natMulFn x.1 y.1) (natMulFn x.2 y.2),
    append (natMulFn x.1 y.2) (natMulFn x.2 y.1))

theorem pairMul_carrier {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    BEDC.Derived.IntUp.IntPairCarrier (pairMul x y).1 (pairMul x y).2 := by
  rcases x with ⟨p, n⟩
  rcases y with ⟨q, m⟩
  exact
    ⟨unary_append_closed (natMulFn_unary hx.left hy.left) (natMulFn_unary hx.right hy.right),
      unary_append_closed (natMulFn_unary hx.left hy.right) (natMulFn_unary hx.right hy.left)⟩

end BEDC.Derived.IntUp
