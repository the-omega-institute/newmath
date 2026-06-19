namespace BEDC.Derived.Window6ParryModPDescent

def goldenDiscriminant : Int :=
  (-1 : Int) ^ 2 - 4 * (1 : Int) * (-1 : Int)

theorem golden_minpoly_disc_five : goldenDiscriminant = 5 := by
  decide

def goldenEvalMod (p r : Nat) : Nat :=
  (r * r + (p - 1) * r + (p - 1)) % p

def rootsMod (p : Nat) : List Nat :=
  (List.range p).filter (fun r => goldenEvalMod p r == 0)

def hasRootMod (p : Nat) : Bool :=
  (rootsMod p).length != 0

def noRootMod (p : Nat) : Bool :=
  (rootsMod p).length == 0

def inertPrimeNoRootRows : List (Nat × Bool × List Nat) :=
  [2, 3, 7, 13].map (fun p => (p, noRootMod p, rootsMod p))

theorem inert_primes_irreducible :
    inertPrimeNoRootRows =
      [(2, true, []), (3, true, []), (7, true, []), (13, true, [])] := by
  decide

def splitPrimeRootRows : List (Nat × Bool × List Nat) :=
  [11, 19, 29, 31].map (fun p => (p, hasRootMod p, rootsMod p))

theorem split_primes_have_root :
    splitPrimeRootRows =
      [(11, true, [4, 8]), (19, true, [5, 15]), (29, true, [6, 24]), (31, true, [13, 19])] := by
  decide

def goldenCoeffsMod (p : Nat) : List Nat :=
  [(p - 1) % p, (p - 1) % p, 1 % p]

def squareXPlusCMod (p c : Nat) : List Nat :=
  [(c * c) % p, (2 * c) % p, 1 % p]

def ramifiedFiveData : List Nat × List Nat × List Nat :=
  (goldenCoeffsMod 5, squareXPlusCMod 5 2, rootsMod 5)

theorem ramified_five_double_root :
    ramifiedFiveData = ([4, 4, 1], [4, 4, 1], [3]) := by
  decide

def normalizationDenom : Nat :=
  10

theorem normalization_denom_div_five : 5 ∣ normalizationDenom := by
  exact ⟨2, by decide⟩

def projectiveKernelEquationMod (p a : Nat) : Bool :=
  let w0 := (a * a) % p
  let w1 := 1 % p
  ((w0 + a * w1) % p == (a * w0) % p) && (w0 == (a * a * w1) % p)

def splitProjectiveKernelRows : List (Nat × Nat × Bool) :=
  [11, 19, 29, 31].foldl
    (fun acc p => acc ++ (rootsMod p).map (fun r => (p, r, projectiveKernelEquationMod p r)))
    []

def ramifiedProjectiveKernelRow : Nat × Nat × Bool :=
  (5, 3, projectiveKernelEquationMod 5 3)

theorem projective_kernel_survives_split_and_ramified :
    splitProjectiveKernelRows =
        [(11, 4, true), (11, 8, true), (19, 5, true), (19, 15, true),
         (29, 6, true), (29, 24, true), (31, 13, true), (31, 19, true)] ∧
      ramifiedProjectiveKernelRow = (5, 3, true) := by
  decide

end BEDC.Derived.Window6ParryModPDescent
