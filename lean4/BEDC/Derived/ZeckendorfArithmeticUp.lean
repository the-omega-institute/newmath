import BEDC.Derived.ZeckendorfUp

namespace BEDC.Derived.ZeckendorfArithmeticUp

open BEDC.Derived.ZeckendorfUp

abbrev ZeckendorfWord : Type :=
  List Nat

def value (indices : ZeckendorfWord) : Nat :=
  zeckendorfValue indices

def normalize (indices : ZeckendorfWord) : ZeckendorfWord :=
  zeckendorf (value indices)

def zeckAddRaw (left right : ZeckendorfWord) : ZeckendorfWord :=
  left ++ right

def zeckAdd (left right : ZeckendorfWord) : ZeckendorfWord :=
  normalize (zeckAddRaw left right)

def zeckOfNat (n : Nat) : ZeckendorfWord :=
  zeckendorf n

def canonical (indices : ZeckendorfWord) : Prop :=
  indices = zeckendorf (value indices)

theorem value_nil :
    value [] = 0 := by
  rfl

theorem value_cons (index : Nat) (rest : ZeckendorfWord) :
    value (index :: rest) = fibonacciTerm index + value rest := by
  rfl

theorem value_append (left right : ZeckendorfWord) :
    value (left ++ right) = value left + value right := by
  induction left with
  | nil =>
      rw [List.nil_append, value_nil, Nat.zero_add]
  | cons index rest ih =>
      rw [List.cons_append, value_cons, value_cons, ih, Nat.add_assoc]

theorem normalize_value (indices : ZeckendorfWord) :
    value (normalize indices) = value indices := by
  unfold normalize value
  exact zeckendorf_sum_restore (zeckendorfValue indices)

theorem normalize_legal (indices : ZeckendorfWord) :
    ZeckendorfLegal (normalize indices) := by
  unfold normalize value
  exact zeckendorf_legal (zeckendorfValue indices)

theorem normalize_canonical (indices : ZeckendorfWord) :
    canonical (normalize indices) := by
  unfold canonical normalize value
  rw [zeckendorf_sum_restore]

theorem zeckOfNat_value (n : Nat) :
    value (zeckOfNat n) = n := by
  exact zeckendorf_sum_restore n

theorem value_zeck (n : Nat) :
    value (zeckendorf n) = n := by
  exact zeckendorf_sum_restore n

theorem zeck_value_roundtrip (indices : ZeckendorfWord) :
    value (zeckendorf (value indices)) = value indices := by
  exact zeckendorf_sum_restore (value indices)

theorem zeck_raw_add_value (left right : ZeckendorfWord) :
    value (zeckAddRaw left right) = value left + value right := by
  exact value_append left right

theorem zeck_add_value (left right : ZeckendorfWord) :
    value (zeckAdd left right) = value left + value right := by
  unfold zeckAdd
  rw [normalize_value, zeck_raw_add_value]

theorem zeck_add_legal (left right : ZeckendorfWord) :
    ZeckendorfLegal (zeckAdd left right) := by
  unfold zeckAdd
  exact normalize_legal (zeckAddRaw left right)

theorem zeck_add_canonical (left right : ZeckendorfWord) :
    canonical (zeckAdd left right) := by
  unfold zeckAdd
  exact normalize_canonical (zeckAddRaw left right)

theorem normalize_raw_add_eq_zeck_value_sum (left right : ZeckendorfWord) :
    normalize (zeckAddRaw left right) = zeckendorf (value left + value right) := by
  unfold normalize zeckAddRaw
  rw [value_append]

theorem zeck_add_correct (a b : Nat) :
    zeckAdd (zeckOfNat a) (zeckOfNat b) = zeckOfNat (a + b) := by
  unfold zeckAdd
  rw [normalize_raw_add_eq_zeck_value_sum, zeckOfNat_value, zeckOfNat_value]
  rfl

theorem zeck_add_value_correct (a b : Nat) :
    value (zeckAdd (zeckOfNat a) (zeckOfNat b)) = a + b := by
  rw [zeck_add_value, zeckOfNat_value, zeckOfNat_value]

end BEDC.Derived.ZeckendorfArithmeticUp
