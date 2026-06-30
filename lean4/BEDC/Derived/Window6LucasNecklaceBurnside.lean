import BEDC.Derived.Window6LucasCount

namespace BEDC.Derived.Window6LucasNecklaceBurnside

open BEDC.Derived.Window6Lucas (lucas)

/-- Euler totient: count of 1 <= k <= n coprime to n. -/
def eulerPhi (n : Nat) : Nat :=
  ((List.range n).map (fun k => k + 1)).foldl
    (fun acc k => if Nat.gcd k n == 1 then acc + 1 else acc) 0

/-- Positive divisors of n, listed as 1 <= d <= n with d | n. -/
def divisors (n : Nat) : List Nat :=
  ((List.range n).map (fun k => k + 1)).filter (fun d => n % d == 0)

/-- Burnside divisor sum `sum_{d|m} phi(d) * L(m/d)`. -/
def burnsideSum (m : Nat) : Nat :=
  (divisors m).foldl (fun acc d => acc + eulerPhi d * lucas (m / d)) 0

theorem eulerPhi_one : eulerPhi 1 = 1 := rfl

theorem eulerPhi_six : eulerPhi 6 = 2 := rfl

theorem divisors_twelve : divisors 12 = [1, 2, 3, 4, 6, 12] := rfl

theorem burnsideSum_one : burnsideSum 1 = 1 := rfl

theorem burnside_identity_1 : burnsideSum 1 = 1 * 1 := rfl

theorem burnside_identity_2 : burnsideSum 2 = 2 * 2 := rfl

theorem burnside_identity_3 : burnsideSum 3 = 3 * 2 := rfl

theorem burnside_identity_4 : burnsideSum 4 = 4 * 3 := rfl

theorem burnside_identity_5 : burnsideSum 5 = 5 * 3 := rfl

theorem burnside_identity_6 : burnsideSum 6 = 6 * 5 := rfl

theorem burnside_identity_7 : burnsideSum 7 = 7 * 5 := rfl

theorem burnside_identity_8 : burnsideSum 8 = 8 * 8 := rfl

theorem burnside_identity_9 : burnsideSum 9 = 9 * 10 := rfl

theorem burnside_identity_10 : burnsideSum 10 = 10 * 15 := rfl

theorem burnside_identity_11 : burnsideSum 11 = 11 * 19 := rfl

theorem burnside_identity_12 : burnsideSum 12 = 12 * 31 := rfl

theorem burnside_identity_13 : burnsideSum 13 = 13 * 41 := rfl

theorem burnside_identity_14 : burnsideSum 14 = 14 * 64 := rfl

theorem burnside_identity_15 : burnsideSum 15 = 15 * 94 := rfl

/-- Burnside orbit-count integrality `m * N_m = sum_{d|m} phi(d) L(m/d)` for cyclic
    Fibonacci necklaces, witnessed over m = 1..15. -/
theorem lucas_necklace_burnside_identity :
    burnsideSum 1 = 1 * 1 ∧ burnsideSum 2 = 2 * 2 ∧ burnsideSum 3 = 3 * 2 ∧
    burnsideSum 4 = 4 * 3 ∧ burnsideSum 5 = 5 * 3 ∧ burnsideSum 6 = 6 * 5 ∧
    burnsideSum 7 = 7 * 5 ∧ burnsideSum 8 = 8 * 8 ∧ burnsideSum 9 = 9 * 10 ∧
    burnsideSum 10 = 10 * 15 ∧ burnsideSum 11 = 11 * 19 ∧ burnsideSum 12 = 12 * 31 ∧
    burnsideSum 13 = 13 * 41 ∧ burnsideSum 14 = 14 * 64 ∧ burnsideSum 15 = 15 * 94 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.Window6LucasNecklaceBurnside
