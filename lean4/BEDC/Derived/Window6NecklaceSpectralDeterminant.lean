import BEDC.Derived.Window6TraceCycleIndexNecklace

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6NecklaceSpectralDeterminant

open BEDC.Derived.Window6TraceCycleIndexNecklace

structure BiPolyTerm where
  xPow : Nat
  yPow : Nat
  coeff : Int
deriving DecidableEq, Repr

def biCoeffAt (p : List BiPolyTerm) (xPow yPow : Nat) : Int :=
  p.foldl
    (fun acc term =>
      if term.xPow == xPow && term.yPow == yPow then acc + term.coeff else acc)
    0

def biBounds (p : List BiPolyTerm) : Nat × Nat :=
  p.foldl
    (fun acc term =>
      if term.coeff == 0 then acc else (Nat.max acc.fst term.xPow, Nat.max acc.snd term.yPow))
    (0, 0)

def biNormalize (p : List BiPolyTerm) : List BiPolyTerm :=
  let bounds := biBounds p
  ((List.range (bounds.fst + 1)).foldl
    (fun acc xPow =>
      acc ++
        ((List.range (bounds.snd + 1)).map
          (fun yPow => { xPow := xPow, yPow := yPow, coeff := biCoeffAt p xPow yPow })).filter
            (fun term => term.coeff != 0))
    [])

def biAdd (p q : List BiPolyTerm) : List BiPolyTerm :=
  biNormalize (p ++ q)

def biNeg (p : List BiPolyTerm) : List BiPolyTerm :=
  p.map (fun term => { term with coeff := -term.coeff })

def biSub (p q : List BiPolyTerm) : List BiPolyTerm :=
  biAdd p (biNeg q)

def biMul (p q : List BiPolyTerm) : List BiPolyTerm :=
  biNormalize
    (p.foldl
      (fun acc a =>
        acc ++ q.map
          (fun b =>
            { xPow := a.xPow + b.xPow
              yPow := a.yPow + b.yPow
              coeff := a.coeff * b.coeff }))
      [])

def biOne : List BiPolyTerm :=
  [{ xPow := 0, yPow := 0, coeff := 1 }]

def biX : List BiPolyTerm :=
  [{ xPow := 1, yPow := 0, coeff := 1 }]

def biXY : List BiPolyTerm :=
  [{ xPow := 1, yPow := 1, coeff := 1 }]

structure BiMat where
  a00 : List BiPolyTerm
  a01 : List BiPolyTerm
  a10 : List BiPolyTerm
  a11 : List BiPolyTerm
deriving DecidableEq, Repr

def det2 (A : BiMat) : List BiPolyTerm :=
  biSub (biMul A.a00 A.a11) (biMul A.a01 A.a10)

def IMinusXWeightedTransfer : BiMat :=
  { a00 := biSub biOne biX
    a01 := biNeg biXY
    a10 := biNeg biX
    a11 := biOne }

def detIMinusXWeightedTransfer : List BiPolyTerm :=
  det2 IMinusXWeightedTransfer

def expectedSpectralDet : List BiPolyTerm :=
  [{ xPow := 0, yPow := 0, coeff := 1 },
   { xPow := 1, yPow := 0, coeff := -1 },
   { xPow := 2, yPow := 1, coeff := -1 }]

theorem det_I_minus_xT :
    biNormalize detIMinusXWeightedTransfer = expectedSpectralDet := by
  decide

def newtonNecklaceRhs (g : Nat) : List Int :=
  polyTrim
    ((divisors g).foldl
      (fun acc d =>
        polyAdd acc
          (polyScale (Int.ofNat d)
            (polySubstPow (primitivePoly d) (g / d))))
      [])

def newtonNecklaceRows : List (Nat × List Int × List Int) :=
  (List.range 10).map
    (fun i =>
      let g := i + 1
      (g, weightedTrace g, newtonNecklaceRhs g))

def newtonNecklacePowerSumCheck : Bool :=
  newtonNecklaceRows.all (fun row => row.snd.fst == row.snd.snd)

theorem newton_necklace_powersum :
    newtonNecklacePowerSumCheck = true := by
  decide

def c10RawEulerTermsComputed : List ((Nat × Nat) × Int) :=
  (divisors 10).foldl
    (fun acc d =>
      let p := primitivePoly d
      acc ++
        ((List.range p.length).map
          (fun s => ((d, s), coeffAt p s))).filter
            (fun row => row.snd != 0))
    []

def c10RawEulerTermsExpected : List ((Nat × Nat) × Int) :=
  [((1, 0), 1), ((2, 1), 1), ((5, 1), 1), ((5, 2), 1),
   ((10, 1), 1), ((10, 2), 3), ((10, 3), 5), ((10, 4), 2)]

def c10SectorLiftToKernel (terms : List ((Nat × Nat) × Int)) : List ((Nat × Nat) × Int) :=
  terms.map (fun row => ((row.fst.fst, row.fst.snd * (10 / row.fst.fst)), row.snd))

def c10EulerExponentsCheck : Bool :=
  c10RawEulerTermsComputed == c10RawEulerTermsExpected &&
    c10SectorLiftToKernel c10RawEulerTermsComputed == kernelTermsG10Computed

theorem c10_euler_exponents :
    c10EulerExponentsCheck = true := by
  decide

def zOneTracePowerRows : List (Nat × Int) :=
  (List.range 10).map
    (fun i =>
      let g := i + 1
      (g, traceAtOne (weightedTrace g)))

def zOneLucasPowerSumCheck : Bool :=
  zOneTracePowerRows == lucasTraceRows

theorem z1_lucas_powersum :
    zOneLucasPowerSumCheck = true := by
  decide

end BEDC.Derived.Window6NecklaceSpectralDeterminant
