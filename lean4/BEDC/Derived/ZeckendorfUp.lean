import BEDC.Derived.FibonacciUp
import BEDC.Derived.Window6Zeckendorf

namespace BEDC.Derived.ZeckendorfUp

abbrev fib : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.fib

abbrev zfib : Nat -> Nat :=
  BEDC.Derived.Window6Zeckendorf.zfib

def fibonacciTerm (index : Nat) : Nat :=
  fib (index + 2)

def zeckendorfValue : List Nat -> Nat
  | [] => 0
  | index :: rest => fibonacciTerm index + zeckendorfValue rest

def ZeckendorfBelow (bound : Nat) (indices : List Nat) : Prop :=
  BEDC.Derived.Window6Zeckendorf.ZReprBelow bound indices

def ZeckendorfLegal (indices : List Nat) : Prop :=
  exists bound : Nat, ZeckendorfBelow bound indices

def zeckendorf (n : Nat) : List Nat :=
  BEDC.Derived.Window6Zeckendorf.greedyBelow (n + 2) n

theorem zfib_eq_fibonacciTerm : forall index : Nat, zfib index = fibonacciTerm index
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      change zfib (k + 1) + zfib k = fibonacciTerm (k + 2)
      unfold fibonacciTerm
      rw [zfib_eq_fibonacciTerm (k + 1), zfib_eq_fibonacciTerm k]
      change fib (k + 3) + fib (k + 2) = fib (k + 4)
      rw [show fib (k + 4) = fib (k + 3) + fib (k + 2) by rfl]

theorem zeckendorfValue_eq_zval (indices : List Nat) :
    zeckendorfValue indices = BEDC.Derived.Window6Zeckendorf.zval indices := by
  induction indices with
  | nil =>
      rfl
  | cons index rest ih =>
      rw [zeckendorfValue, BEDC.Derived.Window6Zeckendorf.zval, ih]
      unfold fibonacciTerm
      exact congrArg (fun term => term + BEDC.Derived.Window6Zeckendorf.zval rest)
        (zfib_eq_fibonacciTerm index).symm

theorem zeckendorf_bound (n : Nat) :
    n < zfib (n + 2) :=
  BEDC.Derived.Window6Zeckendorf.zfib_nat_bound n

theorem zeckendorf_spec (n : Nat) :
    ZeckendorfBelow (n + 2) (zeckendorf n) ∧ zeckendorfValue (zeckendorf n) = n := by
  unfold zeckendorf ZeckendorfBelow
  have hspec :=
    BEDC.Derived.Window6Zeckendorf.greedyBelow_spec (n + 2) n
      (zeckendorf_bound n)
  exact And.intro hspec.left ((zeckendorfValue_eq_zval _).trans hspec.right)

theorem zeckendorf_legal (n : Nat) :
    ZeckendorfLegal (zeckendorf n) := by
  exact Exists.intro (n + 2) (zeckendorf_spec n).left

theorem zeckendorf_sum_restore (n : Nat) :
    zeckendorfValue (zeckendorf n) = n :=
  (zeckendorf_spec n).right

theorem zeckendorf_positive_legal (n : Nat) :
    ZeckendorfLegal (zeckendorf (n + 1)) :=
  zeckendorf_legal (n + 1)

theorem zeckendorf_positive_sum_restore (n : Nat) :
    zeckendorfValue (zeckendorf (n + 1)) = n + 1 :=
  zeckendorf_sum_restore (n + 1)

theorem zeckendorf_one :
    zeckendorf 1 = [0] := by
  rfl

theorem zeckendorf_two :
    zeckendorf 2 = [1] := by
  rfl

theorem zeckendorf_three :
    zeckendorf 3 = [2] := by
  rfl

theorem zeckendorf_four :
    zeckendorf 4 = [2, 0] := by
  rfl

theorem zeckendorf_hundred :
    zeckendorf 100 = [9, 4, 2] := by
  rfl

end BEDC.Derived.ZeckendorfUp
