/-
Finite Zeckendorf-window Mobius arithmetic certificate.

For Fibonacci numbers F_0 = 0, F_1 = 1, F_{n+2} = F_{n+1} + F_n, the file
computes the Zeckendorf Hamming weight s_Z(N), the squarefree
Zeckendorf-Hamming polynomial SQ_m = sum mu(N)^2 u^{s_Z(N)}, the signed
companion M_m = sum mu(N) u^{s_Z(N)}, the squarefree sieve
mu(n)^2 = sum_{d^2 | n} mu(d), and finite Mertens-cancellation certificates
(sum mu(N))^2 <= F_{m+2}. These are finite-window certificates mirroring the
RH-equivalent M(x) = O(x^{1/2}) shape; they are not an RH proof.
-/

namespace BEDC.Derived.ZeckendorfMobiusSieve

set_option maxRecDepth 20000

def fib : Nat -> Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

def largestFibLeAux (n idx best : Nat) : Nat -> Nat
| 0 => best
| fuel + 1 =>
    let f := fib idx
    if f <= n then
      largestFibLeAux n (idx + 1) idx fuel
    else
      best

def largestFibLe (n : Nat) : Nat :=
  largestFibLeAux n 2 1 (n + 3)

def zeckWeightFuel : Nat -> Nat -> Nat
| _, 0 => 0
| 0, _ + 1 => 0
| n, fuel + 1 =>
    let k := largestFibLe n
    1 + zeckWeightFuel (n - fib k) fuel

def zeckWeight (N : Nat) : Nat :=
  zeckWeightFuel N (N + 1)

theorem zeckWeight_6 : zeckWeight 6 = 2 := by
  rfl

theorem zeckWeight_7 : zeckWeight 7 = 2 := by
  rfl

theorem zeckWeight_12 : zeckWeight 12 = 3 := by
  rfl

def dividesNat (d n : Nat) : Bool :=
  if d == 0 then
    false
  else
    n % d == 0

def hasSquareDivisorFrom (n d : Nat) : Nat -> Bool
| 0 => false
| fuel + 1 =>
    let sq := d * d
    if n < sq then
      false
    else if dividesNat sq n then
      true
    else
      hasSquareDivisorFrom n (d + 1) fuel

def isSquarefree (n : Nat) : Bool :=
  if n == 0 then
    false
  else
    !(hasSquareDivisorFrom n 2 (n + 1))

def primeFactorCountAux (n d acc : Nat) : Nat -> Nat
| 0 => acc
| fuel + 1 =>
    if n < d * d then
      if n == 1 then acc else acc + 1
    else if dividesNat d n then
      primeFactorCountAux (n / d) (d + 1) (acc + 1) fuel
    else
      primeFactorCountAux n (d + 1) acc fuel

def primeFactorCount (n : Nat) : Nat :=
  primeFactorCountAux n 2 0 (n + 1)

def negOnePow : Nat -> Int
| 0 => 1
| n + 1 => -(negOnePow n)

def muVal (n : Nat) : Int :=
  if n == 0 then
    0
  else if isSquarefree n then
    negOnePow (primeFactorCount n)
  else
    0

theorem muVal_6 : muVal 6 = 1 := by
  rfl

theorem muVal_4 : muVal 4 = 0 := by
  rfl

theorem muVal_30 : muVal 30 = -1 := by
  rfl

theorem isSquarefree_4 : isSquarefree 4 = false := by
  rfl

theorem isSquarefree_6 : isSquarefree 6 = true := by
  rfl

abbrev IPoly := List Int

def allZero : IPoly -> Bool
| [] => true
| a :: as =>
    if a == 0 then
      allZero as
    else
      false

def trimTrailingZeros : IPoly -> IPoly
| [] => []
| a :: as =>
    if allZero as then
      if a == 0 then [] else [a]
    else
      a :: trimTrailingZeros as

def addMonomialRaw : Nat -> Int -> IPoly -> IPoly
| 0, coeff, [] => [coeff]
| 0, coeff, a :: as => (a + coeff) :: as
| k + 1, coeff, [] => 0 :: addMonomialRaw k coeff []
| k + 1, coeff, a :: as => a :: addMonomialRaw k coeff as

def addMonomial (k : Nat) (coeff : Int) (p : IPoly) : IPoly :=
  trimTrailingZeros (addMonomialRaw k coeff p)

def foldSQWindow (stop : Nat) : Nat -> IPoly -> IPoly
| 0, p => p
| fuel + 1, p =>
    let n := stop - (fuel + 1)
    let coeff : Int := if isSquarefree n then 1 else 0
    foldSQWindow stop fuel (addMonomial (zeckWeight n) coeff p)

def foldMWindow (stop : Nat) : Nat -> IPoly -> IPoly
| 0, p => p
| fuel + 1, p =>
    let n := stop - (fuel + 1)
    foldMWindow stop fuel (addMonomial (zeckWeight n) (muVal n) p)

def SQ (m : Nat) : IPoly :=
  let stop := fib (m + 2)
  foldSQWindow stop (stop - 1) []

def Msigned (m : Nat) : IPoly :=
  let stop := fib (m + 2)
  foldMWindow stop (stop - 1) []

theorem SQ_m1 : SQ 1 = [0, 1] := by
  rfl

theorem SQ_m2 : SQ 2 = [0, 2] := by
  rfl

theorem SQ_m3 : SQ 3 = [0, 3] := by
  rfl

theorem SQ_m4 : SQ 4 = [0, 4, 2] := by
  rfl

theorem SQ_m5 : SQ 5 = [0, 4, 4] := by
  rfl

theorem SQ_m6 : SQ 6 = [0, 5, 6, 2] := by
  rfl

theorem SQ_m7 : SQ 7 = [0, 6, 10, 4, 1] := by
  rfl

theorem SQ_m8 : SQ 8 = [0, 7, 15, 7, 4] := by
  rfl

theorem Msigned_m1 : Msigned 1 = [0, 1] := by
  rfl

theorem Msigned_m2 : Msigned 2 = [] := by
  rfl

theorem Msigned_m3 : Msigned 3 = [0, -1] := by
  rfl

theorem Msigned_m4 : Msigned 4 = [0, -2] := by
  rfl

theorem Msigned_m5 : Msigned 5 = [0, -2] := by
  rfl

theorem Msigned_m6 : Msigned 6 = [0, -3, 2, -2] := by
  rfl

theorem Msigned_m7 : Msigned 7 = [0, -2, 2, -4, 1] := by
  rfl

theorem Msigned_m8 : Msigned 8 = [0, -1, 1, -5, 2] := by
  rfl

def sieveSumFrom (n d : Nat) : Nat -> Int
| 0 => 0
| fuel + 1 =>
    let sq := d * d
    if n < sq then
      0
    else
      let rest := sieveSumFrom n (d + 1) fuel
      if dividesNat sq n then
        muVal d + rest
      else
        rest

def sieveSum (n : Nat) : Int :=
  sieveSumFrom n 1 (n + 1)

theorem musq_sieve_1 : (if isSquarefree 1 then (1 : Int) else 0) = sieveSum 1 := by
  rfl

theorem musq_sieve_2 : (if isSquarefree 2 then (1 : Int) else 0) = sieveSum 2 := by
  rfl

theorem musq_sieve_3 : (if isSquarefree 3 then (1 : Int) else 0) = sieveSum 3 := by
  rfl

theorem musq_sieve_4 : (if isSquarefree 4 then (1 : Int) else 0) = sieveSum 4 := by
  rfl

theorem musq_sieve_5 : (if isSquarefree 5 then (1 : Int) else 0) = sieveSum 5 := by
  rfl

theorem musq_sieve_6 : (if isSquarefree 6 then (1 : Int) else 0) = sieveSum 6 := by
  rfl

theorem musq_sieve_7 : (if isSquarefree 7 then (1 : Int) else 0) = sieveSum 7 := by
  rfl

theorem musq_sieve_8 : (if isSquarefree 8 then (1 : Int) else 0) = sieveSum 8 := by
  rfl

theorem musq_sieve_9 : (if isSquarefree 9 then (1 : Int) else 0) = sieveSum 9 := by
  rfl

theorem musq_sieve_10 : (if isSquarefree 10 then (1 : Int) else 0) = sieveSum 10 := by
  rfl

theorem musq_sieve_11 : (if isSquarefree 11 then (1 : Int) else 0) = sieveSum 11 := by
  rfl

theorem musq_sieve_12 : (if isSquarefree 12 then (1 : Int) else 0) = sieveSum 12 := by
  rfl

theorem musq_sieve_13 : (if isSquarefree 13 then (1 : Int) else 0) = sieveSum 13 := by
  rfl

theorem musq_sieve_14 : (if isSquarefree 14 then (1 : Int) else 0) = sieveSum 14 := by
  rfl

theorem musq_sieve_15 : (if isSquarefree 15 then (1 : Int) else 0) = sieveSum 15 := by
  rfl

theorem musq_sieve_16 : (if isSquarefree 16 then (1 : Int) else 0) = sieveSum 16 := by
  rfl

theorem musq_sieve_17 : (if isSquarefree 17 then (1 : Int) else 0) = sieveSum 17 := by
  rfl

theorem musq_sieve_18 : (if isSquarefree 18 then (1 : Int) else 0) = sieveSum 18 := by
  rfl

theorem musq_sieve_19 : (if isSquarefree 19 then (1 : Int) else 0) = sieveSum 19 := by
  rfl

theorem musq_sieve_20 : (if isSquarefree 20 then (1 : Int) else 0) = sieveSum 20 := by
  rfl

def foldMsumWindow (stop : Nat) : Nat -> Int -> Int
| 0, acc => acc
| fuel + 1, acc =>
    let n := stop - (fuel + 1)
    foldMsumWindow stop fuel (acc + muVal n)

def Msum (m : Nat) : Int :=
  let stop := fib (m + 2)
  foldMsumWindow stop (stop - 1) 0

def mertensSlack : Nat -> Nat
| 1 => 1
| 2 => 3
| 3 => 4
| 4 => 4
| 5 => 9
| 6 => 12
| 7 => 25
| 8 => 46
| 9 => 88
| 10 => 143
| 11 => 233
| 12 => 368
| _ => 0

theorem mertens_slack_1 :
    (Msum 1) * (Msum 1) + Int.ofNat (mertensSlack 1) = Int.ofNat (fib (1 + 2)) := by
  rfl

theorem mertens_slack_2 :
    (Msum 2) * (Msum 2) + Int.ofNat (mertensSlack 2) = Int.ofNat (fib (2 + 2)) := by
  rfl

theorem mertens_slack_3 :
    (Msum 3) * (Msum 3) + Int.ofNat (mertensSlack 3) = Int.ofNat (fib (3 + 2)) := by
  rfl

theorem mertens_slack_4 :
    (Msum 4) * (Msum 4) + Int.ofNat (mertensSlack 4) = Int.ofNat (fib (4 + 2)) := by
  rfl

theorem mertens_slack_5 :
    (Msum 5) * (Msum 5) + Int.ofNat (mertensSlack 5) = Int.ofNat (fib (5 + 2)) := by
  rfl

theorem mertens_slack_6 :
    (Msum 6) * (Msum 6) + Int.ofNat (mertensSlack 6) = Int.ofNat (fib (6 + 2)) := by
  rfl

theorem mertens_slack_7 :
    (Msum 7) * (Msum 7) + Int.ofNat (mertensSlack 7) = Int.ofNat (fib (7 + 2)) := by
  rfl

theorem mertens_slack_8 :
    (Msum 8) * (Msum 8) + Int.ofNat (mertensSlack 8) = Int.ofNat (fib (8 + 2)) := by
  rfl

theorem mertens_slack_9 :
    (Msum 9) * (Msum 9) + Int.ofNat (mertensSlack 9) = Int.ofNat (fib (9 + 2)) := by
  rfl

theorem mertens_slack_10 :
    (Msum 10) * (Msum 10) + Int.ofNat (mertensSlack 10) = Int.ofNat (fib (10 + 2)) := by
  rfl

theorem mertens_slack_11 :
    (Msum 11) * (Msum 11) + Int.ofNat (mertensSlack 11) = Int.ofNat (fib (11 + 2)) := by
  rfl

theorem mertens_slack_12 :
    (Msum 12) * (Msum 12) + Int.ofNat (mertensSlack 12) = Int.ofNat (fib (12 + 2)) := by
  rfl

def intSquareNat : Int -> Nat
| Int.ofNat n => n * n
| Int.negSucc n => (n + 1) * (n + 1)

def MsumSquare (m : Nat) : Nat :=
  intSquareNat (Msum m)

theorem mertens_bound_1 : MsumSquare 1 + mertensSlack 1 = fib (1 + 2) := by
  rfl

theorem mertens_bound_2 : MsumSquare 2 + mertensSlack 2 = fib (2 + 2) := by
  rfl

theorem mertens_bound_3 : MsumSquare 3 + mertensSlack 3 = fib (3 + 2) := by
  rfl

theorem mertens_bound_4 : MsumSquare 4 + mertensSlack 4 = fib (4 + 2) := by
  rfl

theorem mertens_bound_5 : MsumSquare 5 + mertensSlack 5 = fib (5 + 2) := by
  rfl

theorem mertens_bound_6 : MsumSquare 6 + mertensSlack 6 = fib (6 + 2) := by
  rfl

theorem mertens_bound_7 : MsumSquare 7 + mertensSlack 7 = fib (7 + 2) := by
  rfl

theorem mertens_bound_8 : MsumSquare 8 + mertensSlack 8 = fib (8 + 2) := by
  rfl

theorem mertens_bound_9 : MsumSquare 9 + mertensSlack 9 = fib (9 + 2) := by
  rfl

theorem mertens_bound_10 : MsumSquare 10 + mertensSlack 10 = fib (10 + 2) := by
  rfl

theorem mertens_bound_11 : MsumSquare 11 + mertensSlack 11 = fib (11 + 2) := by
  rfl

theorem mertens_bound_12 : MsumSquare 12 + mertensSlack 12 = fib (12 + 2) := by
  rfl

theorem zeckendorf_mobius_sieve_certificate :
    zeckWeight 6 = 2 ∧
    zeckWeight 12 = 3 ∧
    muVal 30 = -1 ∧
    isSquarefree 6 = true ∧
    SQ 8 = [0, 7, 15, 7, 4] ∧
    Msigned 8 = [0, -1, 1, -5, 2] ∧
    (if isSquarefree 20 then (1 : Int) else 0) = sieveSum 20 ∧
    MsumSquare 12 + mertensSlack 12 = fib (12 + 2) := by
  constructor
  · exact zeckWeight_6
  constructor
  · exact zeckWeight_12
  constructor
  · exact muVal_30
  constructor
  · exact isSquarefree_6
  constructor
  · exact SQ_m8
  constructor
  · exact Msigned_m8
  constructor
  · exact musq_sieve_20
  · exact mertens_bound_12

end BEDC.Derived.ZeckendorfMobiusSieve
