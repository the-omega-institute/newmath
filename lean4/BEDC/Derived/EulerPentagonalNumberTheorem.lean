/-
Euler's pentagonal number theorem

  product_{n >= 1} (1 - q^n)
    = sum_{k in Z} (-1)^k q^(k * (3 * k - 1) / 2)

is recorded here as an exact finite NameCert reconstruction.  The generating
function side is truncated to the polynomial product
product_{n=1}^{30} (1 - q^n), and the certificate checks coefficients through
degree 26.  The Franklin side enumerates distinct-part partitions and records
the finite signed count sum_lambda (-1)^(#lambda) through n = 12.  No axiom is
introduced; all displayed equalities are kernel reduction over finite data.
-/

namespace BEDC.Derived.EulerPentagonalNumberTheorem

set_option maxRecDepth 2000

abbrev QPoly := List Int

def qpadd : QPoly -> QPoly -> QPoly
| [], q => q
| p, [] => p
| a :: p, b :: q => (a + b) :: qpadd p q

def qpscale (a : Int) : QPoly -> QPoly
| [] => []
| b :: q => (a * b) :: qpscale a q

def qpmul : QPoly -> QPoly -> QPoly
| [], _ => []
| a :: p, q => qpadd (qpscale a q) (0 :: qpmul p q)

def qptrunc : Nat -> QPoly -> QPoly
| 0, _ => []
| _, [] => []
| n + 1, a :: p => a :: qptrunc n p

def qpmulTrunc (limit : Nat) (p q : QPoly) : QPoly :=
  qptrunc limit (qpmul p q)

def zeroes : Nat -> QPoly
| 0 => []
| n + 1 => 0 :: zeroes n

def factorPoly (n : Nat) : QPoly :=
  1 :: zeroes (n - 1) ++ [-1]

def coeffAt : QPoly -> Nat -> Int
| [], _ => 0
| a :: _, 0 => a
| _ :: p, d + 1 => coeffAt p d

def mulFactorCoeff (p : QPoly) (n d : Nat) : Int :=
  coeffAt p d - if n <= d then coeffAt p (d - n) else 0

def mulFactorWindowFrom (p : QPoly) (n : Nat) : Nat -> Nat -> QPoly
| _, 0 => []
| d, m + 1 => mulFactorCoeff p n d :: mulFactorWindowFrom p n (d + 1) m

def mulFactorWindow (p : QPoly) (n limit : Nat) : QPoly :=
  mulFactorWindowFrom p n 0 limit

def pentProd : Nat -> QPoly
| 0 => [1]
| n + 1 => mulFactorWindow (pentProd n) (n + 1) 27

def signNat : Nat -> Int
| 0 => 1
| n + 1 => -signNat n

def pentagonalMinus (k : Nat) : Nat :=
  k * (3 * k - 1) / 2

def pentagonalPlus (k : Nat) : Nat :=
  k * (3 * k + 1) / 2

def pentSignSearch (d : Nat) : Nat -> Int
| 0 =>
    if pentagonalMinus 0 == d then
      signNat 0
    else if pentagonalPlus 0 == d then
      signNat 0
    else
      0
| k + 1 =>
    if pentagonalMinus (k + 1) == d then
      signNat (k + 1)
    else if pentagonalPlus (k + 1) == d then
      signNat (k + 1)
    else
      pentSignSearch d k

def pentSign (d : Nat) : Int :=
  pentSignSearch d d

def eulerPentagonalCoeffTable : List Int :=
  [1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 1]

def pentSignTable : Nat -> List Int
| 0 => [pentSign 0]
| n + 1 => pentSignTable n ++ [pentSign (n + 1)]

theorem euler_pentagonal_coeffs :
    ((pentProd 30).take 27 == eulerPentagonalCoeffTable) = true := by
  rfl

theorem euler_pentagonal_sign_table :
    (pentSignTable 26 == eulerPentagonalCoeffTable) = true := by
  rfl

theorem euler_pentagonal_gf_0 : coeffAt (pentProd 30) 0 = pentSign 0 := by
  rfl

theorem euler_pentagonal_gf_1 : coeffAt (pentProd 30) 1 = pentSign 1 := by
  rfl

theorem euler_pentagonal_gf_2 : coeffAt (pentProd 30) 2 = pentSign 2 := by
  rfl

theorem euler_pentagonal_gf_3 : coeffAt (pentProd 30) 3 = pentSign 3 := by
  rfl

theorem euler_pentagonal_gf_4 : coeffAt (pentProd 30) 4 = pentSign 4 := by
  rfl

theorem euler_pentagonal_gf_5 : coeffAt (pentProd 30) 5 = pentSign 5 := by
  rfl

theorem euler_pentagonal_gf_6 : coeffAt (pentProd 30) 6 = pentSign 6 := by
  rfl

theorem euler_pentagonal_gf_7 : coeffAt (pentProd 30) 7 = pentSign 7 := by
  rfl

theorem euler_pentagonal_gf_8 : coeffAt (pentProd 30) 8 = pentSign 8 := by
  rfl

theorem euler_pentagonal_gf_9 : coeffAt (pentProd 30) 9 = pentSign 9 := by
  rfl

theorem euler_pentagonal_gf_10 : coeffAt (pentProd 30) 10 = pentSign 10 := by
  rfl

theorem euler_pentagonal_gf_11 : coeffAt (pentProd 30) 11 = pentSign 11 := by
  rfl

theorem euler_pentagonal_gf_12 : coeffAt (pentProd 30) 12 = pentSign 12 := by
  rfl

theorem euler_pentagonal_gf_13 : coeffAt (pentProd 30) 13 = pentSign 13 := by
  rfl

theorem euler_pentagonal_gf_14 : coeffAt (pentProd 30) 14 = pentSign 14 := by
  rfl

theorem euler_pentagonal_gf_15 : coeffAt (pentProd 30) 15 = pentSign 15 := by
  rfl

theorem euler_pentagonal_gf_16 : coeffAt (pentProd 30) 16 = pentSign 16 := by
  rfl

theorem euler_pentagonal_gf_17 : coeffAt (pentProd 30) 17 = pentSign 17 := by
  rfl

theorem euler_pentagonal_gf_18 : coeffAt (pentProd 30) 18 = pentSign 18 := by
  rfl

theorem euler_pentagonal_gf_19 : coeffAt (pentProd 30) 19 = pentSign 19 := by
  rfl

theorem euler_pentagonal_gf_20 : coeffAt (pentProd 30) 20 = pentSign 20 := by
  rfl

theorem euler_pentagonal_gf_21 : coeffAt (pentProd 30) 21 = pentSign 21 := by
  rfl

theorem euler_pentagonal_gf_22 : coeffAt (pentProd 30) 22 = pentSign 22 := by
  rfl

theorem euler_pentagonal_gf_23 : coeffAt (pentProd 30) 23 = pentSign 23 := by
  rfl

theorem euler_pentagonal_gf_24 : coeffAt (pentProd 30) 24 = pentSign 24 := by
  rfl

theorem euler_pentagonal_gf_25 : coeffAt (pentProd 30) 25 = pentSign 25 := by
  rfl

theorem euler_pentagonal_gf_26 : coeffAt (pentProd 30) 26 = pentSign 26 := by
  rfl

def distinctPartitionsAtMost : Nat -> Nat -> List (List Nat)
| n, 0 =>
    if n == 0 then
      [[]]
    else
      []
| n, m + 1 =>
    let withoutHead := distinctPartitionsAtMost n m
    let withHead :=
      if m + 1 <= n then
        (distinctPartitionsAtMost (n - (m + 1)) m).map (fun p => (m + 1) :: p)
      else
        []
    withHead ++ withoutHead

def distinctPartitions (n : Nat) : List (List Nat) :=
  distinctPartitionsAtMost n n

def partSign : List Nat -> Int
| [] => 1
| _ :: p => -partSign p

def signedCountList : List (List Nat) -> Int
| [] => 0
| p :: ps => partSign p + signedCountList ps

def signedCount (n : Nat) : Int :=
  signedCountList (distinctPartitions n)

theorem distinctPartitions_5 :
    distinctPartitions 5 = [[5], [4, 1], [3, 2]] := by
  rfl

theorem signedCount_5_concrete : signedCount 5 = 1 := by
  rfl

theorem franklin_signed_count_0 : signedCount 0 = pentSign 0 := by
  rfl

theorem franklin_signed_count_1 : signedCount 1 = pentSign 1 := by
  rfl

theorem franklin_signed_count_2 : signedCount 2 = pentSign 2 := by
  rfl

theorem franklin_signed_count_3 : signedCount 3 = pentSign 3 := by
  rfl

theorem franklin_signed_count_4 : signedCount 4 = pentSign 4 := by
  rfl

theorem franklin_signed_count_5 : signedCount 5 = pentSign 5 := by
  rfl

theorem franklin_signed_count_6 : signedCount 6 = pentSign 6 := by
  rfl

theorem franklin_signed_count_7 : signedCount 7 = pentSign 7 := by
  rfl

theorem franklin_signed_count_8 : signedCount 8 = pentSign 8 := by
  rfl

theorem franklin_signed_count_9 : signedCount 9 = pentSign 9 := by
  rfl

theorem franklin_signed_count_10 : signedCount 10 = pentSign 10 := by
  rfl

theorem franklin_signed_count_11 : signedCount 11 = pentSign 11 := by
  rfl

theorem franklin_signed_count_12 : signedCount 12 = pentSign 12 := by
  rfl

theorem euler_pentagonal_number_theorem_certificate :
    ((pentProd 30).take 27 == eulerPentagonalCoeffTable) = true ∧
    (pentSignTable 26 == eulerPentagonalCoeffTable) = true ∧
    signedCount 0 = pentSign 0 ∧
    signedCount 1 = pentSign 1 ∧
    signedCount 2 = pentSign 2 ∧
    signedCount 3 = pentSign 3 ∧
    signedCount 4 = pentSign 4 ∧
    signedCount 5 = pentSign 5 ∧
    signedCount 6 = pentSign 6 ∧
    signedCount 7 = pentSign 7 ∧
    signedCount 8 = pentSign 8 ∧
    signedCount 9 = pentSign 9 ∧
    signedCount 10 = pentSign 10 ∧
    signedCount 11 = pentSign 11 ∧
    signedCount 12 = pentSign 12 := by
  constructor
  · exact euler_pentagonal_coeffs
  constructor
  · exact euler_pentagonal_sign_table
  constructor
  · exact franklin_signed_count_0
  constructor
  · exact franklin_signed_count_1
  constructor
  · exact franklin_signed_count_2
  constructor
  · exact franklin_signed_count_3
  constructor
  · exact franklin_signed_count_4
  constructor
  · exact franklin_signed_count_5
  constructor
  · exact franklin_signed_count_6
  constructor
  · exact franklin_signed_count_7
  constructor
  · exact franklin_signed_count_8
  constructor
  · exact franklin_signed_count_9
  constructor
  · exact franklin_signed_count_10
  constructor
  · exact franklin_signed_count_11
  · exact franklin_signed_count_12

end BEDC.Derived.EulerPentagonalNumberTheorem
