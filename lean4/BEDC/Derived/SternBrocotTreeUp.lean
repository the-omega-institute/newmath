import BEDC.Derived.FibonacciUp
import BEDC.Derived.SternBrocotUp

namespace BEDC.Derived.SternBrocotTreeUp

open BEDC.Derived.SternBrocotUp

private theorem nat_sum_pair_shift (a b : Nat) :
    a + b + (1 + 1) = a + 1 + (b + 1) := by
  calc
    a + b + (1 + 1) = a + (b + (1 + 1)) := Nat.add_assoc a b (1 + 1)
    _ = a + ((b + 1) + 1) :=
      congrArg (fun t => a + t) (Nat.add_assoc b 1 1).symm
    _ = a + ((1 + b) + 1) :=
      congrArg (fun t => a + (t + 1)) (Nat.add_comm b 1)
    _ = a + (1 + (b + 1)) :=
      congrArg (fun t => a + t) (Nat.add_assoc 1 b 1)
    _ = a + 1 + (b + 1) := (Nat.add_assoc a 1 (b + 1)).symm

/-- 区间载体只保存相邻端点；`adjacent` 即 $bc-ad=1$ 的 BEDC 整数关系形式。 -/
structure SternBrocotInterval where
  left : PositiveFraction
  right : PositiveFraction
  adjacent : FareyAdjacent left right

def intervalMediant (I : SternBrocotInterval) : PositiveFraction :=
  mediant I.left I.right

def leftInterval (I : SternBrocotInterval) : SternBrocotInterval :=
  { left := I.left
    right := intervalMediant I
    adjacent := fareyAdjacent_left_mediant I.adjacent }

def rightInterval (I : SternBrocotInterval) : SternBrocotInterval :=
  { left := intervalMediant I
    right := I.right
    adjacent := fareyAdjacent_mediant_right I.adjacent }

theorem interval_unimodular (I : SternBrocotInterval) :
    IntRel (crossDet I.left I.right) intRing.one := by
  exact fareyAdjacent_cross_eq_one I.adjacent

theorem left_interval_unimodular (I : SternBrocotInterval) :
    IntRel (crossDet (leftInterval I).left (leftInterval I).right) intRing.one := by
  exact interval_unimodular (leftInterval I)

theorem right_interval_unimodular (I : SternBrocotInterval) :
    IntRel (crossDet (rightInterval I).left (rightInterval I).right) intRing.one := by
  exact interval_unimodular (rightInterval I)

theorem mediant_neighbor_unimodular (I : SternBrocotInterval) :
    FareyAdjacent I.left (intervalMediant I) ∧
      FareyAdjacent (intervalMediant I) I.right := by
  exact fareyAdjacent_mediant_neighbors I.adjacent

/-- 在不引入商构造的导出层中，约化性以存在 unimodular 邻点表达。 -/
def AdjacentReduced (x : PositiveFraction) : Prop :=
  ∃ y : PositiveFraction, FareyAdjacent x y ∨ FareyAdjacent y x

theorem mediant_adjacency_reduced (I : SternBrocotInterval) :
    AdjacentReduced (intervalMediant I) := by
  exact ⟨I.right, Or.inl (fareyAdjacent_mediant_right I.adjacent)⟩

inductive Branch where
  | left
  | right
  deriving DecidableEq

abbrev BranchPath := List Branch

/-- Calkin-Wilf 的正分数载体以前驱自然数保存，实际值为 `(numPred+1)/(denPred+1)`。 -/
structure CWPositiveFraction where
  numPred : Nat
  denPred : Nat
  deriving DecidableEq

def cwNumerator (x : CWPositiveFraction) : Nat :=
  x.numPred + 1

def cwDenominator (x : CWPositiveFraction) : Nat :=
  x.denPred + 1

def cwRoot : CWPositiveFraction :=
  { numPred := 0, denPred := 0 }

def cwLeft (x : CWPositiveFraction) : CWPositiveFraction :=
  { numPred := x.numPred
    denPred := x.numPred + x.denPred + 1 }

def cwRight (x : CWPositiveFraction) : CWPositiveFraction :=
  { numPred := x.numPred + x.denPred + 1
    denPred := x.denPred }

theorem cw_left_readback (x : CWPositiveFraction) :
    cwNumerator (cwLeft x) = cwNumerator x ∧
      cwDenominator (cwLeft x) = cwNumerator x + cwDenominator x := by
  constructor
  · rfl
  · unfold cwDenominator cwNumerator cwLeft
    exact nat_sum_pair_shift x.numPred x.denPred

theorem cw_right_readback (x : CWPositiveFraction) :
    cwNumerator (cwRight x) = cwNumerator x + cwDenominator x ∧
      cwDenominator (cwRight x) = cwDenominator x := by
  constructor
  · unfold cwNumerator cwDenominator cwRight
    exact nat_sum_pair_shift x.numPred x.denPred
  · rfl

def cwStep : Branch -> CWPositiveFraction -> CWPositiveFraction
  | Branch.left, x => cwLeft x
  | Branch.right, x => cwRight x

def cwPair (x : CWPositiveFraction) : Nat × Nat :=
  (cwNumerator x, cwDenominator x)

def cwPairStep : Branch -> Nat × Nat -> Nat × Nat
  | Branch.left, pair => (pair.1, pair.1 + pair.2)
  | Branch.right, pair => (pair.1 + pair.2, pair.2)

theorem cwStep_pair (step : Branch) (x : CWPositiveFraction) :
    cwPair (cwStep step x) = cwPairStep step (cwPair x) := by
  cases step with
  | left =>
      have read := cw_left_readback x
      unfold cwPair cwPairStep
      exact Prod.ext read.left read.right
  | right =>
      have read := cw_right_readback x
      unfold cwPair cwPairStep
      exact Prod.ext read.left read.right

def cwEval : BranchPath -> CWPositiveFraction
  | [] => cwRoot
  | step :: tail => cwStep step (cwEval tail)

theorem cwEval_nil : cwEval [] = cwRoot := by
  rfl

theorem cwEval_cons_left (tail : BranchPath) :
    cwEval (Branch.left :: tail) = cwLeft (cwEval tail) := by
  rfl

theorem cwEval_cons_right (tail : BranchPath) :
    cwEval (Branch.right :: tail) = cwRight (cwEval tail) := by
  rfl

def cwChildren (x : CWPositiveFraction) : List CWPositiveFraction :=
  [cwLeft x, cwRight x]

def cwNextLevel : List CWPositiveFraction -> List CWPositiveFraction
  | [] => []
  | x :: xs => cwChildren x ++ cwNextLevel xs

def calkinWilfLevel : Nat -> List CWPositiveFraction
  | 0 => [cwRoot]
  | fuel + 1 => cwNextLevel (calkinWilfLevel fuel)

def calkinWilfPrefix : Nat -> List CWPositiveFraction
  | 0 => []
  | fuel + 1 => calkinWilfPrefix fuel ++ calkinWilfLevel fuel

theorem calkinWilfLevel_zero :
    calkinWilfLevel 0 = [cwRoot] := by
  rfl

theorem calkinWilfLevel_succ (fuel : Nat) :
    calkinWilfLevel (fuel + 1) = cwNextLevel (calkinWilfLevel fuel) := by
  rfl

theorem calkinWilfPrefix_succ (fuel : Nat) :
    calkinWilfPrefix (fuel + 1) = calkinWilfPrefix fuel ++ calkinWilfLevel fuel := by
  rfl

inductive GeneratedPositiveRational : CWPositiveFraction -> Prop where
  | root : GeneratedPositiveRational cwRoot
  | left {x : CWPositiveFraction} :
      GeneratedPositiveRational x -> GeneratedPositiveRational (cwLeft x)
  | right {x : CWPositiveFraction} :
      GeneratedPositiveRational x -> GeneratedPositiveRational (cwRight x)

theorem cwEval_generated (path : BranchPath) :
    GeneratedPositiveRational (cwEval path) := by
  induction path with
  | nil =>
      exact GeneratedPositiveRational.root
  | cons step tail ih =>
      cases step with
      | left =>
          exact GeneratedPositiveRational.left ih
      | right =>
          exact GeneratedPositiveRational.right ih

theorem generated_has_path {x : CWPositiveFraction} :
    GeneratedPositiveRational x -> ∃ path : BranchPath, cwEval path = x := by
  intro generated
  induction generated with
  | root =>
      exact ⟨[], rfl⟩
  | left _ ih =>
      cases ih with
      | intro path eqPath =>
          exact ⟨Branch.left :: path, congrArg cwLeft eqPath⟩
  | right _ ih =>
      cases ih with
      | intro path eqPath =>
          exact ⟨Branch.right :: path, congrArg cwRight eqPath⟩

/-- 非商构造的正分数规格；`numPred/denPred` 是实际分子分母的前驱。 -/
structure PositiveFractionSpec where
  numPred : Nat
  denPred : Nat

def PositiveFractionSpec.num (x : PositiveFractionSpec) : Nat :=
  x.numPred + 1

def PositiveFractionSpec.den (x : PositiveFractionSpec) : Nat :=
  x.denPred + 1

def PositiveFractionSpec.toCW (x : PositiveFractionSpec) : CWPositiveFraction :=
  { numPred := x.numPred, denPred := x.denPred }

theorem positiveFractionSpec_toCW_readback (x : PositiveFractionSpec) :
    cwNumerator x.toCW = x.num ∧ cwDenominator x.toCW = x.den := by
  exact ⟨rfl, rfl⟩

inductive PositivePairGenerated : Nat -> Nat -> Prop where
  | root : PositivePairGenerated 1 1
  | left {a b : Nat} :
      PositivePairGenerated a b -> PositivePairGenerated a (a + b)
  | right {a b : Nat} :
      PositivePairGenerated a b -> PositivePairGenerated (a + b) b

theorem positivePairGenerated_positive_left {a b : Nat} :
    PositivePairGenerated a b -> 0 < a := by
  intro generated
  induction generated with
  | root =>
      exact Nat.succ_pos 0
  | left _ ih =>
      exact ih
  | right _ ih =>
      exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)

theorem positivePairGenerated_positive_right {a b : Nat} :
    PositivePairGenerated a b -> 0 < b := by
  intro generated
  induction generated with
  | root =>
      exact Nat.succ_pos 0
  | left _ ih =>
      exact Nat.lt_of_lt_of_le ih (Nat.le_add_left _ _)
  | right _ ih =>
      exact ih

theorem cwEval_positivePairGenerated (path : BranchPath) :
    PositivePairGenerated (cwNumerator (cwEval path)) (cwDenominator (cwEval path)) := by
  induction path with
  | nil =>
      exact PositivePairGenerated.root
  | cons step tail ih =>
      cases step with
      | left =>
          have read := cw_left_readback (cwEval tail)
          change
            PositivePairGenerated
              (cwNumerator (cwLeft (cwEval tail)))
              (cwDenominator (cwLeft (cwEval tail)))
          rw [read.left, read.right]
          exact PositivePairGenerated.left ih
      | right =>
          have read := cw_right_readback (cwEval tail)
          change
            PositivePairGenerated
              (cwNumerator (cwRight (cwEval tail)))
              (cwDenominator (cwRight (cwEval tail)))
          rw [read.left, read.right]
          exact PositivePairGenerated.right ih

theorem cwEval_positive_left (path : BranchPath) :
    0 < cwNumerator (cwEval path) := by
  exact positivePairGenerated_positive_left (cwEval_positivePairGenerated path)

theorem cwEval_positive_right (path : BranchPath) :
    0 < cwDenominator (cwEval path) := by
  exact positivePairGenerated_positive_right (cwEval_positivePairGenerated path)

theorem generatedPositiveRational_positive_left {x : CWPositiveFraction} :
    GeneratedPositiveRational x -> 0 < cwNumerator x := by
  intro generated
  cases generated_has_path generated with
  | intro path same =>
      cases same
      exact cwEval_positive_left path

theorem generatedPositiveRational_positive_right {x : CWPositiveFraction} :
    GeneratedPositiveRational x -> 0 < cwDenominator x := by
  intro generated
  cases generated_has_path generated with
  | intro path same =>
      cases same
      exact cwEval_positive_right path

def pairOfPositiveFractionSpec (x : PositiveFractionSpec) : Nat × Nat :=
  (x.num, x.den)

def pairCoveredByCalkinWilf (pair : Nat × Nat) : Prop :=
  ∃ path : BranchPath, cwPair (cwEval path) = pair

theorem cwEval_pairCovered (path : BranchPath) :
    pairCoveredByCalkinWilf (cwPair (cwEval path)) := by
  exact ⟨path, rfl⟩

theorem positivePairGenerated_has_path {a b : Nat} :
    PositivePairGenerated a b -> ∃ path : BranchPath, cwPair (cwEval path) = (a, b) := by
  intro generated
  induction generated with
  | root =>
      exact ⟨[], rfl⟩
  | left gen ih =>
      cases ih with
      | intro path same =>
          exact ⟨Branch.left :: path, by
            rw [cwEval_cons_left]
            have read := cw_left_readback (cwEval path)
            unfold cwPair at same
            cases same
            unfold cwPair
            apply Prod.ext
            · exact read.left
            · exact read.right⟩
  | right gen ih =>
      cases ih with
      | intro path same =>
          exact ⟨Branch.right :: path, by
            rw [cwEval_cons_right]
            have read := cw_right_readback (cwEval path)
            unfold cwPair at same
            cases same
            unfold cwPair
            apply Prod.ext
            · exact read.left
            · exact read.right⟩

def positiveFractionSpecCoveredByCalkinWilf (x : PositiveFractionSpec) : Prop :=
  pairCoveredByCalkinWilf (pairOfPositiveFractionSpec x)

theorem positiveFractionSpec_has_cw_path
    (x : PositiveFractionSpec) :
    PositivePairGenerated x.num x.den -> positiveFractionSpecCoveredByCalkinWilf x := by
  intro generated
  exact positivePairGenerated_has_path generated

def fibonacciLevelPair (n : Nat) : Nat × Nat :=
  (BEDC.Derived.FibonacciUp.fib (n + 1),
    BEDC.Derived.FibonacciUp.fib (n + 2))

theorem fibonacciLevelPair_first_successor (n : Nat) :
    (fibonacciLevelPair (n + 1)).1 =
      (fibonacciLevelPair n).2 := by
  unfold fibonacciLevelPair
  rfl

theorem fibonacciLevelPair_second_successor (n : Nat) :
    (fibonacciLevelPair (n + 1)).2 =
      (fibonacciLevelPair n).2 + (fibonacciLevelPair n).1 := by
  unfold fibonacciLevelPair
  rw [BEDC.Derived.FibonacciUp.fib_recurrence (n + 1)]

end BEDC.Derived.SternBrocotTreeUp
