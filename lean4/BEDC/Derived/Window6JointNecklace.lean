import BEDC.Derived.Window6WeightedNecklace

set_option maxRecDepth 4096

namespace BEDC.Derived.Window6JointNecklace

abbrev rotateWord : Nat → Nat → Nat → Nat :=
  BEDC.Derived.Window6WeightedNecklace.rotateWord

abbrev canonicalOrbitWords : Nat → List Nat :=
  BEDC.Derived.Window6WeightedNecklace.canonicalOrbitWords

abbrev weightOf : Nat → Nat → Nat :=
  BEDC.Derived.Window6WeightedNecklace.weightOf

/-
The period-ten golden clock has a gauge-invariant bivariate spectrum:
each basepoint-free C_10 orbit is graded jointly by its exact orbit size
and its Hamming weight.  This finite certificate is about the golden-necklace
program only; it makes no claim about physical alpha.
-/

def containsNat (needle : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => if x == needle then true else containsNat needle xs

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => if containsNat x xs then dedupNat xs else x :: dedupNat xs

def rotationsOf (m w : Nat) : List Nat :=
  (List.range m).map (fun shift => rotateWord m shift w)

def orbitSizeOf (m w : Nat) : Nat :=
  (dedupNat (rotationsOf m w)).length

def jointCount (m d k : Nat) : Nat :=
  (canonicalOrbitWords m).filter
    (fun w => (orbitSizeOf m w == d) && (weightOf m w == k))
    |>.length

def jointClassesP10 : List (Nat × Nat) :=
  [(1, 0), (2, 5), (5, 2), (5, 4), (10, 1), (10, 2), (10, 3), (10, 4)]

def jointSpectrumFor (m : Nat) (classes : List (Nat × Nat)) :
    List ((Nat × Nat) × Nat) :=
  classes.map (fun dk => (dk, jointCount m dk.fst dk.snd))

def jointSpectrumP10 : List ((Nat × Nat) × Nat) :=
  jointSpectrumFor 10 jointClassesP10

def jointSpectrumTotal (spectrum : List ((Nat × Nat) × Nat)) : Nat :=
  spectrum.foldl (fun acc row => acc + row.snd) 0

def sizeMarginalCount (spectrum : List ((Nat × Nat) × Nat)) (d : Nat) : Nat :=
  (spectrum.filter (fun row => row.fst.fst == d)).foldl
    (fun acc row => acc + row.snd)
    0

def weightMarginalCount (spectrum : List ((Nat × Nat) × Nat)) (k : Nat) : Nat :=
  (spectrum.filter (fun row => row.fst.snd == k)).foldl
    (fun acc row => acc + row.snd)
    0

def sizeMarginalP10 : List (Nat × Nat) :=
  [(1, sizeMarginalCount jointSpectrumP10 1),
   (2, sizeMarginalCount jointSpectrumP10 2),
   (5, sizeMarginalCount jointSpectrumP10 5),
   (10, sizeMarginalCount jointSpectrumP10 10)]

def weightMarginalP10 : List Nat :=
  (List.range 6).map (fun k => weightMarginalCount jointSpectrumP10 k)

theorem jointSpectrum_p10 :
    jointSpectrumP10 =
      [((1, 0), 1), ((2, 5), 1), ((5, 2), 1), ((5, 4), 1),
       ((10, 1), 1), ((10, 2), 3), ((10, 3), 5), ((10, 4), 2)] := by
  decide

theorem jointSpectrum_sum_eq_15 :
    jointSpectrumTotal jointSpectrumP10 = 15 := by
  decide

theorem jointSpectrum_size_marginal_p10 :
    sizeMarginalP10 = [(1, 1), (2, 1), (5, 2), (10, 11)] := by
  decide

theorem jointSpectrum_weight_marginal_p10 :
    weightMarginalP10 = [1, 1, 4, 5, 3, 1] := by
  decide

end BEDC.Derived.Window6JointNecklace
