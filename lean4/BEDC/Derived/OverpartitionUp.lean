import BEDC.Derived.PartitionUp

namespace BEDC.Derived.OverpartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty
abbrev UnaryTwo : BHist := BHist.e1 UnaryOne
abbrev UnaryFour : BHist := BHist.e1 (BHist.e1 UnaryTwo)
abbrev UnaryEight : BHist := BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 UnaryFour)))
abbrev UnaryFourteen : BHist :=
  BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 UnaryEight)))))

inductive Overmark : Type where
  | plain : Overmark
  | markedLast : Overmark

structure Overpart where
  part : Nat
  mark : Overmark

def overpartWeight (p : Overpart) : Nat :=
  p.part

-- 同一部件递减扫描时, `markedLast` 只允许出现在该部件块的最后一次。
def lastMarkedBlock (part : Nat) : Nat -> List Overpart
  | 0 => []
  | Nat.succ copies =>
      let plainCopies := repeatPlain part copies
      plainCopies ++ [{ part := part, mark := Overmark.markedLast }]

where
  repeatPlain (part : Nat) : Nat -> List Overpart
    | 0 => []
    | Nat.succ copies =>
        { part := part, mark := Overmark.plain } :: repeatPlain part copies

def plainBlock (part : Nat) : Nat -> List Overpart
  | 0 => []
  | Nat.succ copies =>
      { part := part, mark := Overmark.plain } :: plainBlock part copies

def overpartitionBlockChoices (part maxCopies : Nat) : List (List Overpart) :=
  plainChoices part maxCopies ++ markedChoices part maxCopies

where
  plainChoices (part : Nat) : Nat -> List (List Overpart)
    | 0 => [[]]
    | Nat.succ copies =>
        plainChoices part copies ++ [plainBlock part (Nat.succ copies)]

  markedChoices (part : Nat) : Nat -> List (List Overpart)
    | 0 => []
    | Nat.succ copies =>
        markedChoices part copies ++ [lastMarkedBlock part (Nat.succ copies)]

def appendBlockToTails (block : List Overpart) : List (List Overpart) -> List (List Overpart)
  | [] => []
  | tail :: tails => (block ++ tail) :: appendBlockToTails block tails

def appendBlocks : List (List Overpart) -> List (List Overpart) -> List (List Overpart)
  | [], _tails => []
  | block :: blocks, tails => appendBlockToTails block tails ++ appendBlocks blocks tails

def overpartitionBlocksForCopies (part : Nat) : Nat -> List (List Overpart)
  | 0 => [[]]
  | Nat.succ copies =>
      [plainBlock part (Nat.succ copies), lastMarkedBlock part (Nat.succ copies)]

def overpartitionListsForCopiesWith
    (smaller : Nat -> List (List Overpart)) (remaining part copies : Nat) :
    List (List Overpart) :=
  if copies * part <= remaining then
    appendBlocks (overpartitionBlocksForCopies part copies)
      (smaller (remaining - copies * part))
  else
    []

def overpartitionCopyScanWith
    (smaller : Nat -> List (List Overpart)) (remaining part : Nat) :
    Nat -> Nat -> List (List Overpart)
  | _copies, 0 => []
  | copies, Nat.succ scanFuel =>
      overpartitionListsForCopiesWith smaller remaining part copies ++
        overpartitionCopyScanWith smaller remaining part (Nat.succ copies) scanFuel

def overpartitionListsFrom : Nat -> Nat -> Nat -> List (List Overpart)
  | _remaining, _maxPart, 0 => []
  | 0, _maxPart, Nat.succ _fuel => [[]]
  | Nat.succ _remaining, 0, Nat.succ _fuel => []
  | Nat.succ remaining, Nat.succ maxPart, Nat.succ fuel =>
      overpartitionCopyScanWith
        (fun nextRemaining => overpartitionListsFrom nextRemaining maxPart fuel)
        (Nat.succ remaining) (Nat.succ maxPart) 0
        (Nat.succ (Nat.succ remaining))

def overpartitionFuelBudget (n : Nat) : Nat :=
  2 * n + 1

def overpartitionLists (n : Nat) : List (List Overpart) :=
  overpartitionListsFrom n n (overpartitionFuelBudget n)

def countList {A : Type u} : List A -> Nat
  | [] => 0
  | _ :: xs => Nat.succ (countList xs)

def countWhere {A : Type u} (p : A -> Bool) : List A -> Nat
  | [] => 0
  | x :: xs =>
      if p x then Nat.succ (countWhere p xs) else countWhere p xs

def overpartitionListCount (n : Nat) : Nat :=
  countList (overpartitionLists n)

def overpartitionBaseCoeff : Nat -> Nat
  | 0 => 1
  | Nat.succ _degree => 0

def overpartitionCoeffScan
    (part degree : Nat) (previous : Nat -> Nat) : Nat -> Nat
  | 0 => previous degree
  | Nat.succ fuel =>
      overpartitionCoeffScan part degree previous fuel +
        if Nat.succ fuel * part <= degree then
          2 * previous (degree - Nat.succ fuel * part)
        else
          0

def overpartitionRowFromPrevious
    (part : Nat) (previous : Nat -> Nat) (degree : Nat) : Nat :=
  overpartitionCoeffScan part degree previous degree

-- 递推表示有限截断生成函数 `∏_{i=1}^{factorCount} (1+q^i)/(1-q^i)` 的系数。
def overpartitionGeneratingCoeff : Nat -> Nat -> Nat
  | 0, degree => overpartitionBaseCoeff degree
  | Nat.succ last, degree =>
      overpartitionRowFromPrevious (Nat.succ last)
        (overpartitionGeneratingCoeff last) degree

def overpartitionNumber (n : Nat) : Nat :=
  overpartitionGeneratingCoeff n n

def overpartitionNumberUp (n : BHist) : BHist :=
  natToUnary (overpartitionNumber (BEDC.FKernel.ExternalBinary.bwordLength n))

def overpartitionCoeffWindowFrom :
    Nat -> Nat -> Nat -> List Nat
  | _factorCount, _start, 0 => []
  | factorCount, start, Nat.succ fuel =>
      overpartitionGeneratingCoeff factorCount start ::
        overpartitionCoeffWindowFrom factorCount (Nat.succ start) fuel

def overpartitionCoeffWindow (factorCount maxDegree : Nat) : List Nat :=
  overpartitionCoeffWindowFrom factorCount 0 (Nat.succ maxDegree)

def overpartitionNumberWindowFrom :
    Nat -> Nat -> List Nat
  | _start, 0 => []
  | start, Nat.succ fuel =>
      overpartitionNumber start :: overpartitionNumberWindowFrom (Nat.succ start) fuel

def overpartitionNumberWindow (maxDegree : Nat) : List Nat :=
  overpartitionNumberWindowFrom 0 (Nat.succ maxDegree)

def coefficientProductFactorCount : Nat := 8

def coefficientWindowMaxDegree : Nat := 8

private theorem listPairwiseEq_refl {A : Type u} :
    (xs : List A) ->
      BEDC.Algebra.FiniteFold.ListPairwiseRel Eq xs xs
  | [] => BEDC.Algebra.FiniteFold.ListPairwiseRel.nil
  | x :: xs =>
      BEDC.Algebra.FiniteFold.ListPairwiseRel.cons
        (Eq.refl x) (listPairwiseEq_refl xs)

theorem lastMarkedBlock_one (part : Nat) :
    lastMarkedBlock part 1 = [{ part := part, mark := Overmark.markedLast }] := by
  rfl

theorem plainBlock_two (part : Nat) :
    plainBlock part 2 =
      [{ part := part, mark := Overmark.plain },
        { part := part, mark := Overmark.plain }] := by
  rfl

theorem overpartitionBlockChoices_one :
    overpartitionBlockChoices 1 1 =
      [[],
        [{ part := 1, mark := Overmark.plain }],
        [{ part := 1, mark := Overmark.markedLast }]] := by
  rfl

theorem overpartitionGeneratingCoeff_zero_degree :
    overpartitionGeneratingCoeff 0 0 = 1 := by
  rfl

theorem overpartitionGeneratingCoeff_zero_positive_degree (degree : Nat) :
    overpartitionGeneratingCoeff 0 (Nat.succ degree) = 0 := by
  rfl

theorem overpartitionGeneratingCoeff_step (last degree : Nat) :
    overpartitionGeneratingCoeff (Nat.succ last) degree =
      overpartitionRowFromPrevious (Nat.succ last)
        (overpartitionGeneratingCoeff last) degree := by
  rfl

theorem overpartitionRowFromPrevious_zero_degree (part : Nat) (previous : Nat -> Nat) :
    overpartitionRowFromPrevious part previous 0 = previous 0 := by
  rfl

theorem overpartitionNumber_definition (n : Nat) :
    overpartitionNumber n = overpartitionGeneratingCoeff n n := by
  rfl

theorem overpartitionNumberUp_unary_result (n : BHist) :
    UnaryHistory (overpartitionNumberUp n) := by
  unfold overpartitionNumberUp
  exact natToUnary_unary _

theorem overpartitionNumber_zero :
    overpartitionNumber 0 = 1 := by
  rfl

theorem overpartitionNumber_one :
    overpartitionNumber 1 = 2 := by
  rfl

theorem overpartitionNumber_two :
    overpartitionNumber 2 = 4 := by
  rfl

theorem overpartitionNumber_three :
    overpartitionNumber 3 = 8 := by
  rfl

theorem overpartitionNumber_four :
    overpartitionNumber 4 = 14 := by
  rfl

theorem overpartitionNumber_five :
    overpartitionNumber 5 = 24 := by
  rfl

theorem overpartitionNumber_six :
    overpartitionNumber 6 = 40 := by
  rfl

theorem overpartitionNumber_seven :
    overpartitionNumber 7 = 64 := by
  rfl

theorem overpartitionNumber_eight :
    overpartitionNumber 8 = 100 := by
  rfl

theorem overpartitionCoeffWindow_small :
    overpartitionCoeffWindow coefficientProductFactorCount coefficientWindowMaxDegree =
      [1, 2, 4, 8, 14, 24, 40, 64, 100] := by
  rfl

theorem overpartitionNumberWindow_small :
    overpartitionNumberWindow 8 =
      [1, 2, 4, 8, 14, 24, 40, 64, 100] := by
  rfl

theorem overpartitionListCount_small :
    [overpartitionListCount 0,
      overpartitionListCount 1,
      overpartitionListCount 2,
      overpartitionListCount 3,
      overpartitionListCount 4] =
      [1, 2, 4, 8, 14] := by
  rfl

theorem overpartitionGeneratingCoeffWindow_matches_number_window :
    BEDC.Algebra.FiniteFold.ListPairwiseRel Eq
      (overpartitionCoeffWindow coefficientProductFactorCount coefficientWindowMaxDegree)
      (overpartitionNumberWindow coefficientWindowMaxDegree) := by
  unfold coefficientProductFactorCount coefficientWindowMaxDegree
  unfold overpartitionCoeffWindow overpartitionCoeffWindowFrom
  unfold overpartitionNumberWindow overpartitionNumberWindowFrom
  exact listPairwiseEq_refl _

theorem overpartitionNumberUp_zero :
    overpartitionNumberUp BHist.Empty = UnaryOne := by
  unfold overpartitionNumberUp
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rfl

theorem overpartitionNumberUp_one :
    overpartitionNumberUp UnaryOne = UnaryTwo := by
  unfold overpartitionNumberUp
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left BHist.Empty
    BEDC.FKernel.Unary.unary_empty]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [overpartitionNumber_one]
  rfl

theorem overpartitionNumberUp_two :
    overpartitionNumberUp UnaryTwo = UnaryFour := by
  unfold overpartitionNumberUp
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left UnaryOne
    (BEDC.FKernel.Unary.unary_e1_closed BEDC.FKernel.Unary.unary_empty)]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left BHist.Empty
    BEDC.FKernel.Unary.unary_empty]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [overpartitionNumber_two]
  rfl

theorem overpartitionNumberUp_three :
    overpartitionNumberUp (natToUnary 3) = UnaryEight := by
  unfold overpartitionNumberUp
  rw [natToUnary_length]
  rw [overpartitionNumber_three]
  rfl

structure OverpartitionFiniteExport : Prop where
  finite_product_step :
    ∀ last degree : Nat,
      overpartitionGeneratingCoeff (Nat.succ last) degree =
        overpartitionRowFromPrevious (Nat.succ last)
          (overpartitionGeneratingCoeff last) degree
  small_values :
    overpartitionNumberWindow 8 =
      [1, 2, 4, 8, 14, 24, 40, 64, 100]
  list_small_values :
    [overpartitionListCount 0,
      overpartitionListCount 1,
      overpartitionListCount 2,
      overpartitionListCount 3,
      overpartitionListCount 4] =
      [1, 2, 4, 8, 14]
  finite_window :
    BEDC.Algebra.FiniteFold.ListPairwiseRel Eq
      (overpartitionCoeffWindow coefficientProductFactorCount coefficientWindowMaxDegree)
      (overpartitionNumberWindow coefficientWindowMaxDegree)
  marked_last_singleton :
    lastMarkedBlock 1 1 = [{ part := 1, mark := Overmark.markedLast }]

theorem OverpartitionUp_finite_export :
    OverpartitionFiniteExport := by
  exact {
    finite_product_step := overpartitionGeneratingCoeff_step
    small_values := overpartitionNumberWindow_small
    list_small_values := overpartitionListCount_small
    finite_window := overpartitionGeneratingCoeffWindow_matches_number_window
    marked_last_singleton := lastMarkedBlock_one 1
  }

#check overpartitionNumber
#check overpartitionGeneratingCoeff
#check overpartitionCoeffWindow
#check overpartitionNumberWindow_small
#check OverpartitionUp_finite_export
#print axioms overpartitionNumber
#print axioms overpartitionGeneratingCoeff
#print axioms overpartitionNumberWindow_small
#print axioms OverpartitionUp_finite_export

end BEDC.Derived.OverpartitionUp
