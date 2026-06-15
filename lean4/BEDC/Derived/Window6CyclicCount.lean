import BEDC.Derived.Window6LucasCount

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6CyclicCount

abbrev lucas : Nat -> Nat :=
  BEDC.Derived.Window6Lucas.lucas

/--
Length-`m` cyclic no-adjacent-one words form the cycle analogue of the
linear stable words counted by Fibonacci numbers.  Their count is the trace
of the transfer matrix power, hence the Lucas number `L_m`; the certificate
below verifies the period-ten clock count `|P_10| = L_10 = 123` by kernel
reduction over the finite bit words, with no extra logical assumptions.
-/

def pow2 : Nat -> Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

def bit (w i : Nat) : Bool :=
  (w / pow2 i) % 2 == 1

def cyclicNoAdjacent (m w : Nat) : Bool :=
  (List.range m).all (fun i => !(bit w i && bit w ((i + 1) % m)))

def P (m : Nat) : List Nat :=
  (List.range (pow2 m)).filter (fun w => cyclicNoAdjacent m w)

def cyclicCount (m : Nat) : Nat :=
  (P m).length

theorem cyclicCount_one : cyclicCount 1 = lucas 1 := by
  rfl

theorem cyclicCount_two : cyclicCount 2 = lucas 2 := by
  rfl

theorem cyclicCount_six : cyclicCount 6 = lucas 6 := by
  rfl

theorem cyclicCount_ten : cyclicCount 10 = 123 := by
  rfl

theorem lucas_ten : lucas 10 = 123 := by
  rfl

theorem cyclicCount_ten_eq_lucas : cyclicCount 10 = lucas 10 := by
  rfl

end BEDC.Derived.Window6CyclicCount
