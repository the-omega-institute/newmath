import BEDC.Derived.Window6JointNecklace

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6TraceCycleIndexNecklace

/-
The trace-cycle-index kernel keeps the transfer-matrix source visible:
`T(z) = [[1,z],[1,0]]` first computes weighted cyclic traces, Mobius extracts
primitive weighted necklaces, and the single kernel `G_10(u,y)` generates the
joint table and its two marginals.  This is finite golden-necklace arithmetic,
not a physical readout claim.
-/

def coeffAt (p : List Int) (k : Nat) : Int :=
  match p, k with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => coeffAt xs n

def polyAdd (p q : List Int) : List Int :=
  (List.range (Nat.max p.length q.length)).map
    (fun k => coeffAt p k + coeffAt q k)

def polyMulLength (p q : List Int) : Nat :=
  if p.isEmpty || q.isEmpty then 0 else p.length + q.length - 1

def polyMul (p q : List Int) : List Int :=
  (List.range (polyMulLength p q)).map
    (fun k =>
      (List.range (k + 1)).foldl
        (fun acc i => acc + coeffAt p i * coeffAt q (k - i))
        0)

structure PolyMat where
  a00 : List Int
  a01 : List Int
  a10 : List Int
  a11 : List Int
deriving DecidableEq, Repr

def matAddEntry (p q r s : List Int) : List Int :=
  polyAdd (polyMul p q) (polyMul r s)

def matMul (A B : PolyMat) : PolyMat :=
  { a00 := matAddEntry A.a00 B.a00 A.a01 B.a10
    a01 := matAddEntry A.a00 B.a01 A.a01 B.a11
    a10 := matAddEntry A.a10 B.a00 A.a11 B.a10
    a11 := matAddEntry A.a10 B.a01 A.a11 B.a11 }

def matOne : PolyMat :=
  { a00 := [1], a01 := [], a10 := [], a11 := [1] }

def weightedTransfer : PolyMat :=
  { a00 := [1], a01 := [0, 1], a10 := [1], a11 := [] }

def matPow (A : PolyMat) : Nat → PolyMat
  | 0 => matOne
  | n + 1 => matMul (matPow A n) A

def tracePoly (A : PolyMat) : List Int :=
  polyAdd A.a00 A.a11

def weightedTrace (g : Nat) : List Int :=
  tracePoly (matPow weightedTransfer g)

def weightedTraceRows : List (Nat × List Int) :=
  (List.range 10).map (fun i => (i + 1, weightedTrace (i + 1)))

def weightedTraceFormulaRows : List (Nat × List Int) :=
  [(1, [1]),
   (2, [1, 2]),
   (3, [1, 3]),
   (4, [1, 4, 2]),
   (5, [1, 5, 5]),
   (6, [1, 6, 9, 2]),
   (7, [1, 7, 14, 7]),
   (8, [1, 8, 20, 16, 2]),
   (9, [1, 9, 27, 30, 9]),
   (10, [1, 10, 35, 50, 25, 2])]

def traceAtOne (p : List Int) : Int :=
  p.foldl (fun acc c => acc + c) 0

def traceAtOneRows : List (Nat × Int) :=
  weightedTraceRows.map (fun row => (row.fst, traceAtOne row.snd))

def lucasTraceRows : List (Nat × Int) :=
  [(1, 1), (2, 3), (3, 4), (4, 7), (5, 11),
   (6, 18), (7, 29), (8, 47), (9, 76), (10, 123)]

def weightedTraceIdentityRowsCheck : Bool :=
  weightedTraceRows == weightedTraceFormulaRows

def weightedTraceZOneLucasRowsCheck : Bool :=
  traceAtOneRows == lucasTraceRows

theorem weighted_trace_identity :
    weightedTraceIdentityRowsCheck = true := by
  decide

theorem weighted_trace_z_one_lucas :
    weightedTraceZOneLucasRowsCheck = true := by
  decide

def polyTrimLength (p : List Int) : Nat :=
  (List.range p.length).foldl
    (fun acc k => if coeffAt p k == 0 then acc else k + 1)
    0

def polyTrim (p : List Int) : List Int :=
  (List.range (polyTrimLength p)).map (fun k => coeffAt p k)

def polyScale (c : Int) (p : List Int) : List Int :=
  polyTrim (p.map (fun x => c * x))

def intAbsNat (x : Int) : Nat :=
  match x with
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

def signedCandidates (bound : Nat) : List Int :=
  let ns := List.range (bound + 1)
  ns.map (fun n => Int.ofNat n) ++ ns.map (fun n => -Int.ofNat n)

def divExactIntByNat (c : Int) (d : Nat) : Int :=
  if d == 0 then 0 else
    (signedCandidates (intAbsNat c + 1)).foldl
      (fun found q => if q * Int.ofNat d == c then q else found)
      0

def polyDivNat (p : List Int) (d : Nat) : List Int :=
  if d == 0 then [] else
    polyTrim (p.map (fun c => divExactIntByNat c d))

def polySubstPowLength (p : List Int) (r : Nat) : Nat :=
  if p.isEmpty then 0 else (p.length - 1) * r + 1

def polySubstPow (p : List Int) (r : Nat) : List Int :=
  polyTrim
    ((List.range (polySubstPowLength p r)).map
      (fun k =>
        (List.range p.length).foldl
          (fun acc i => if i * r == k then acc + coeffAt p i else acc)
          0))

def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun r => r != 0 && n % r == 0)

def hasProperDivisor (n : Nat) : Bool :=
  (List.range n).foldl
    (fun found k =>
      found || (decide (2 <= k) && decide (k < n) && n % k == 0))
    false

def primeBool (n : Nat) : Bool :=
  decide (2 <= n) && !hasProperDivisor n

def primeDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun p => primeBool p && n % p == 0)

def hasSquarePrimeFactor (n : Nat) : Bool :=
  (primeDivisors n).foldl
    (fun found p => found || n % (p * p) == 0)
    false

def mobiusInt (n : Nat) : Int :=
  if n == 1 then 1
  else if hasSquarePrimeFactor n then 0
  else if (primeDivisors n).length % 2 == 0 then 1 else -1

def primitiveNumerator (d : Nat) : List Int :=
  (divisors d).foldl
    (fun acc r =>
      polyAdd acc
        (polyScale (mobiusInt r)
          (polySubstPow (weightedTrace (d / r)) r)))
    []

def primitivePoly (d : Nat) : List Int :=
  polyDivNat (primitiveNumerator d) d

def primitivePolysDvdTenComputed : List (Nat × List Int) :=
  [(1, primitivePoly 1),
   (2, primitivePoly 2),
   (5, primitivePoly 5),
   (10, primitivePoly 10)]

def kernelTermsForDivisor (n d : Nat) : List ((Nat × Nat) × Int) :=
  let p := primitivePoly d
  ((List.range p.length).map
    (fun s => ((d, s * (n / d)), coeffAt p s))).filter
      (fun row => row.snd != 0)

def kernelTermsG10Computed : List ((Nat × Nat) × Int) :=
  (divisors 10).foldl
    (fun acc d => acc ++ kernelTermsForDivisor 10 d)
    []

def coefficientOf (terms : List ((Nat × Nat) × Int)) (d k : Nat) : Int :=
  (terms.filter (fun row => row.fst.fst == d && row.fst.snd == k)).foldl
    (fun acc row => acc + row.snd)
    0

def weightMarginal (terms : List ((Nat × Nat) × Int)) (k : Nat) : Int :=
  (terms.filter (fun row => row.fst.snd == k)).foldl
    (fun acc row => acc + row.snd)
    0

def sizeMarginal (terms : List ((Nat × Nat) × Int)) (d : Nat) : Int :=
  (terms.filter (fun row => row.fst.fst == d)).foldl
    (fun acc row => acc + row.snd)
    0

def totalTerms (terms : List ((Nat × Nat) × Int)) : Int :=
  terms.foldl (fun acc row => acc + row.snd) 0

def recoveredJ10 : List ((Nat × Nat) × Int) :=
  [((1, 0), coefficientOf kernelTermsG10Computed 1 0),
   ((2, 5), coefficientOf kernelTermsG10Computed 2 5),
   ((5, 2), coefficientOf kernelTermsG10Computed 5 2),
   ((5, 4), coefficientOf kernelTermsG10Computed 5 4),
   ((10, 1), coefficientOf kernelTermsG10Computed 10 1),
   ((10, 2), coefficientOf kernelTermsG10Computed 10 2),
   ((10, 3), coefficientOf kernelTermsG10Computed 10 3),
   ((10, 4), coefficientOf kernelTermsG10Computed 10 4)]

def recoveredN10 : List Int :=
  (List.range 6).map (fun k => weightMarginal kernelTermsG10Computed k)

def recoveredSizeSpectrum : List (Nat × Int) :=
  [(1, sizeMarginal kernelTermsG10Computed 1),
   (2, sizeMarginal kernelTermsG10Computed 2),
   (5, sizeMarginal kernelTermsG10Computed 5),
   (10, sizeMarginal kernelTermsG10Computed 10)]

def recoveredOrbitCount : Int :=
  totalTerms kernelTermsG10Computed

theorem primitive_poly_mobius_dvd_ten :
    primitivePolysDvdTenComputed =
      [(1, [1]), (2, [0, 1]), (5, [0, 1, 1]), (10, [0, 1, 3, 5, 2])] := by
  decide

theorem trace_cycle_index_kernel_recovers_J10 :
    recoveredJ10 =
      [((1, 0), 1), ((2, 5), 1), ((5, 2), 1), ((5, 4), 1),
       ((10, 1), 1), ((10, 2), 3), ((10, 3), 5), ((10, 4), 2)] := by
  decide

theorem trace_cycle_index_kernel_recovers_N10 :
    recoveredN10 = [1, 1, 4, 5, 3, 1] := by
  decide

theorem trace_cycle_index_kernel_recovers_size_spectrum :
    recoveredSizeSpectrum = [(1, 1), (2, 1), (5, 2), (10, 11)] := by
  decide

theorem trace_cycle_index_kernel_recovers_orbit_count :
    recoveredOrbitCount = 15 := by
  decide

end BEDC.Derived.Window6TraceCycleIndexNecklace
