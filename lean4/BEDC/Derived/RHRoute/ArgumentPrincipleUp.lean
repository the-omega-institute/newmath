import BEDC.Derived.RHRoute.ZetaZeroLocated

namespace BEDC.Derived.RHRoute.ArgumentPrincipleUp

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete

abbrev Rat : Type :=
  RatNum

structure RationalRectangle where
  left : Rat
  right : Rat
  bottom : Rat
  top : Rat

def RectWellFormed (rect : RationalRectangle) : Prop :=
  ratLe rect.left rect.right ∧ ratLe rect.bottom rect.top

def RectContainsPoint (rect : RationalRectangle) (z : RatComplex) : Prop :=
  ratLe rect.left z.re ∧
    ratLe z.re rect.right ∧
      ratLe rect.bottom z.im ∧
        ratLe z.im rect.top

def RectOnBoundary (rect : RationalRectangle) (z : RatComplex) : Prop :=
  RatEq z.re rect.left ∨
    RatEq z.re rect.right ∨
      RatEq z.im rect.bottom ∨
        RatEq z.im rect.top

def rectangleBottomLeft (rect : RationalRectangle) : RatComplex :=
  { re := rect.left, im := rect.bottom }

def rectangleBottomRight (rect : RationalRectangle) : RatComplex :=
  { re := rect.right, im := rect.bottom }

def rectangleTopRight (rect : RationalRectangle) : RatComplex :=
  { re := rect.right, im := rect.top }

def rectangleTopLeft (rect : RationalRectangle) : RatComplex :=
  { re := rect.left, im := rect.top }

theorem rectangleBottomLeft_in_rect {rect : RationalRectangle} :
    RectWellFormed rect ->
      RectContainsPoint rect (rectangleBottomLeft rect) := by
  intro well
  exact And.intro (ratLe_refl rect.left)
    (And.intro well.left
      (And.intro (ratLe_refl rect.bottom) well.right))

theorem rectangleBottomRight_in_rect {rect : RationalRectangle} :
    RectWellFormed rect ->
      RectContainsPoint rect (rectangleBottomRight rect) := by
  intro well
  exact And.intro well.left
    (And.intro (ratLe_refl rect.right)
      (And.intro (ratLe_refl rect.bottom) well.right))

theorem rectangleTopRight_in_rect {rect : RationalRectangle} :
    RectWellFormed rect ->
      RectContainsPoint rect (rectangleTopRight rect) := by
  intro well
  exact And.intro well.left
    (And.intro (ratLe_refl rect.right)
      (And.intro well.right (ratLe_refl rect.top)))

theorem rectangleTopLeft_in_rect {rect : RationalRectangle} :
    RectWellFormed rect ->
      RectContainsPoint rect (rectangleTopLeft rect) := by
  intro well
  exact And.intro (ratLe_refl rect.left)
    (And.intro well.left
      (And.intro well.right (ratLe_refl rect.top)))

theorem rectangleBottomLeft_on_boundary (rect : RationalRectangle) :
    RectOnBoundary rect (rectangleBottomLeft rect) := by
  exact Or.inl (RatEq_refl rect.left)

theorem rectangleBottomRight_on_boundary (rect : RationalRectangle) :
    RectOnBoundary rect (rectangleBottomRight rect) := by
  exact Or.inr (Or.inl (RatEq_refl rect.right))

theorem rectangleTopRight_on_boundary (rect : RationalRectangle) :
    RectOnBoundary rect (rectangleTopRight rect) := by
  exact Or.inr (Or.inl (RatEq_refl rect.right))

theorem rectangleTopLeft_on_boundary (rect : RationalRectangle) :
    RectOnBoundary rect (rectangleTopLeft rect) := by
  exact Or.inl (RatEq_refl rect.left)

structure ConcreteContourInput (rect : RationalRectangle) where
  point : RatComplex
  input :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  point_eq : input.point = point
  in_rect : RectContainsPoint rect point
  on_boundary : RectOnBoundary rect point

structure RectangleCornerInputs (rect : RationalRectangle) where
  wellformed : RectWellFormed rect
  bottomLeftInput :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  bottomLeft_eq : bottomLeftInput.point = rectangleBottomLeft rect
  bottomRightInput :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  bottomRight_eq : bottomRightInput.point = rectangleBottomRight rect
  topRightInput :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  topRight_eq : topRightInput.point = rectangleTopRight rect
  topLeftInput :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  topLeft_eq : topLeftInput.point = rectangleTopLeft rect

def cornerContourInputs {rect : RationalRectangle}
    (corners : RectangleCornerInputs rect) :
    List (ConcreteContourInput rect) :=
  [ { point := rectangleBottomLeft rect
      input := corners.bottomLeftInput
      point_eq := corners.bottomLeft_eq
      in_rect := rectangleBottomLeft_in_rect corners.wellformed
      on_boundary := rectangleBottomLeft_on_boundary rect },
    { point := rectangleBottomRight rect
      input := corners.bottomRightInput
      point_eq := corners.bottomRight_eq
      in_rect := rectangleBottomRight_in_rect corners.wellformed
      on_boundary := rectangleBottomRight_on_boundary rect },
    { point := rectangleTopRight rect
      input := corners.topRightInput
      point_eq := corners.topRight_eq
      in_rect := rectangleTopRight_in_rect corners.wellformed
      on_boundary := rectangleTopRight_on_boundary rect },
    { point := rectangleTopLeft rect
      input := corners.topLeftInput
      point_eq := corners.topLeft_eq
      in_rect := rectangleTopLeft_in_rect corners.wellformed
      on_boundary := rectangleTopLeft_on_boundary rect } ]

theorem cornerContourInputs_length {rect : RationalRectangle}
    (corners : RectangleCornerInputs rect) :
    (cornerContourInputs corners).length = 4 := by
  rfl

structure BoundaryZetaValue (rect : RationalRectangle) where
  precision : Nat
  point : RatComplex
  input :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ConcreteZetaLocatedInput
  point_eq : input.point = point
  in_rect : RectContainsPoint rect point
  on_boundary : RectOnBoundary rect point
  zetaBox : ComplexBox
  zetaBox_eq :
    zetaBox =
      BEDC.Derived.RHRoute.ZetaZeroLocated.concreteZetaBox input precision
  zeta_fits : concreteBoxGauge.fits zetaBox precision

def sampleAt {rect : RationalRectangle} (precision : Nat)
    (sample : ConcreteContourInput rect) : BoundaryZetaValue rect :=
  { precision := precision
    point := sample.point
    input := sample.input
    point_eq := sample.point_eq
    in_rect := sample.in_rect
    on_boundary := sample.on_boundary
    zetaBox :=
      BEDC.Derived.RHRoute.ZetaZeroLocated.concreteZetaBox
        sample.input precision
    zetaBox_eq := rfl
    zeta_fits :=
      BEDC.Derived.RHRoute.ZetaZeroLocated.concreteZetaBox_fits
        sample.input precision }

def sampleContour {rect : RationalRectangle} (precision : Nat) :
    List (ConcreteContourInput rect) -> List (BoundaryZetaValue rect)
  | [] => []
  | sample :: rest => sampleAt precision sample :: sampleContour precision rest

theorem sampleContour_length {rect : RationalRectangle}
    (precision : Nat) (samples : List (ConcreteContourInput rect)) :
    (sampleContour precision samples).length = samples.length := by
  induction samples with
  | nil =>
      rfl
  | cons sample rest ih =>
      unfold sampleContour
      change Nat.succ (sampleContour precision rest).length =
        Nat.succ rest.length
      rw [ih]

structure ContourTrace (rect : RationalRectangle) where
  precision : Nat
  samples : List (BoundaryZetaValue rect)

def traceFromInputs {rect : RationalRectangle} (precision : Nat)
    (samples : List (ConcreteContourInput rect)) : ContourTrace rect :=
  { precision := precision
    samples := sampleContour precision samples }

def cornerContourTrace {rect : RationalRectangle} (precision : Nat)
    (corners : RectangleCornerInputs rect) : ContourTrace rect :=
  traceFromInputs precision (cornerContourInputs corners)

theorem cornerContourTrace_sample_length {rect : RationalRectangle}
    (precision : Nat) (corners : RectangleCornerInputs rect) :
    (cornerContourTrace precision corners).samples.length = 4 := by
  unfold cornerContourTrace traceFromInputs
  rw [sampleContour_length]
  exact cornerContourInputs_length corners

inductive AxisSign where
  | neg : AxisSign
  | zero : AxisSign
  | pos : AxisSign

def natEqBoolAP : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ x, Nat.succ y => natEqBoolAP x y

def axisSign (q : Rat) : AxisSign :=
  if ratLtBool ratZero q then AxisSign.pos
  else if ratLtBool q ratZero then AxisSign.neg
  else AxisSign.zero

def axisSignCode : AxisSign -> Nat
  | AxisSign.neg => 0
  | AxisSign.zero => 1
  | AxisSign.pos => 2

abbrev PhaseCell : Type :=
  Nat

def phaseNorthEast : PhaseCell :=
  0

def phaseNorthWest : PhaseCell :=
  1

def phaseSouthWest : PhaseCell :=
  2

def phaseSouthEast : PhaseCell :=
  3

def phaseAxis : PhaseCell :=
  4

def phaseCellOfSignCodes (re im : Nat) : PhaseCell :=
  if natEqBoolAP re 2 then
    if natEqBoolAP im 2 then phaseNorthEast
    else if natEqBoolAP im 0 then phaseSouthEast
    else phaseAxis
  else if natEqBoolAP re 0 then
    if natEqBoolAP im 2 then phaseNorthWest
    else if natEqBoolAP im 0 then phaseSouthWest
    else phaseAxis
  else phaseAxis

def phaseCellOfSigns (re im : AxisSign) : PhaseCell :=
  phaseCellOfSignCodes (axisSignCode re) (axisSignCode im)

def phaseCellOfComplex (z : RatComplex) : PhaseCell :=
  phaseCellOfSigns (axisSign z.re) (axisSign z.im)

def phaseCellOfBox (box : ComplexBox) : PhaseCell :=
  phaseCellOfComplex (boxCenter box)

def samplePhase {rect : RationalRectangle}
    (sample : BoundaryZetaValue rect) : PhaseCell :=
  phaseCellOfBox sample.zetaBox

def samplePhaseList {rect : RationalRectangle} :
    List (BoundaryZetaValue rect) -> List PhaseCell
  | [] => []
  | sample :: rest => samplePhase sample :: samplePhaseList rest

def phaseEqBool (a b : PhaseCell) : Bool :=
  natEqBoolAP a b

def phaseChangeWeight (a b : PhaseCell) : Nat :=
  if phaseEqBool a b then 0 else 1

def positiveQuarterTurn (a b : PhaseCell) : Bool :=
  if natEqBoolAP a phaseNorthEast then natEqBoolAP b phaseNorthWest
  else if natEqBoolAP a phaseNorthWest then natEqBoolAP b phaseSouthWest
  else if natEqBoolAP a phaseSouthWest then natEqBoolAP b phaseSouthEast
  else if natEqBoolAP a phaseSouthEast then natEqBoolAP b phaseNorthEast
  else false

def positiveQuarterTurnWeight (a b : PhaseCell) : Nat :=
  if positiveQuarterTurn a b then 1 else 0

theorem positiveQuarterTurnWeight_pos {a b : PhaseCell} :
    positiveQuarterTurn a b = true ->
      0 < positiveQuarterTurnWeight a b := by
  intro h
  unfold positiveQuarterTurnWeight
  rw [h]
  exact Nat.zero_lt_succ 0

def closedPhaseCount (weight : PhaseCell -> PhaseCell -> Nat) :
    List PhaseCell -> Nat
  | [] => 0
  | first :: rest =>
      let rec loop (previous : PhaseCell) : List PhaseCell -> Nat
        | [] => weight previous first
        | current :: tail => weight previous current + loop current tail
      loop first rest

def argumentChangeCountFromPhases (phases : List PhaseCell) : Nat :=
  closedPhaseCount phaseChangeWeight phases

def contourWindingCountFromPhases (phases : List PhaseCell) : Nat :=
  closedPhaseCount positiveQuarterTurnWeight phases

def argumentChangeCount {rect : RationalRectangle}
    (trace : ContourTrace rect) : Nat :=
  argumentChangeCountFromPhases (samplePhaseList trace.samples)

def contourWindingCount {rect : RationalRectangle}
    (trace : ContourTrace rect) : Nat :=
  contourWindingCountFromPhases (samplePhaseList trace.samples)

theorem contourWindingCount_empty (rect : RationalRectangle)
    (precision : Nat) :
    contourWindingCount ({ precision := precision, samples := [] } :
      ContourTrace rect) = 0 := by
  rfl

structure LocatedZeroMark (rect : RationalRectangle) where
  point : RatComplex
  in_rect : RectContainsPoint rect point
  located :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated point

def ContainsLocatedZetaZero (rect : RationalRectangle) : Prop :=
  ∃ point : RatComplex,
    RectContainsPoint rect point ∧
      BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated point

inductive ListContains {α : Type u} (x : α) : List α -> Prop where
  | head {rest : List α} : ListContains x (x :: rest)
  | tail {y : α} {rest : List α} :
      ListContains x rest -> ListContains x (y :: rest)

theorem listContains_of_length_pos {α : Type u} {xs : List α} :
    0 < xs.length -> ∃ x : α, ListContains x xs := by
  cases xs with
  | nil =>
      intro h
      cases h
  | cons x rest =>
      intro _h
      exact Exists.intro x ListContains.head

structure WindingZeroCriterion {rect : RationalRectangle}
    (trace : ContourTrace rect) where
  zeroMarks : List (LocatedZeroMark rect)
  count_matches : zeroMarks.length = contourWindingCount trace

def locatedZeroCount {rect : RationalRectangle} {trace : ContourTrace rect}
    (criterion : WindingZeroCriterion trace) : Nat :=
  criterion.zeroMarks.length

theorem criterion_winding_count_eq_located_zero_count
    {rect : RationalRectangle} {trace : ContourTrace rect}
    (criterion : WindingZeroCriterion trace) :
    contourWindingCount trace = locatedZeroCount criterion := by
  exact criterion.count_matches.symm

theorem marked_zero_of_positive_winding
    {rect : RationalRectangle} {trace : ContourTrace rect}
    (criterion : WindingZeroCriterion trace) :
    0 < contourWindingCount trace ->
      ∃ mark : LocatedZeroMark rect,
        ListContains mark criterion.zeroMarks := by
  intro positive
  have markLengthPositive : 0 < criterion.zeroMarks.length := by
    rw [criterion.count_matches]
    exact positive
  exact listContains_of_length_pos markLengthPositive

theorem positive_count_contains_located_zero
    {rect : RationalRectangle} {trace : ContourTrace rect}
    (criterion : WindingZeroCriterion trace) :
    0 < contourWindingCount trace ->
      ContainsLocatedZetaZero rect := by
  intro positive
  cases marked_zero_of_positive_winding criterion positive with
  | intro mark _membership =>
      exact Exists.intro mark.point
        (And.intro mark.in_rect mark.located)

def ratMid (x y : Rat) : Rat :=
  ratMul (ratAdd x y) halfRat

inductive RectangleBranch where
  | lowerLeft : RectangleBranch
  | lowerRight : RectangleBranch
  | upperLeft : RectangleBranch
  | upperRight : RectangleBranch

def bisectRectangle (rect : RationalRectangle) :
    RectangleBranch -> RationalRectangle
  | RectangleBranch.lowerLeft =>
      { left := rect.left
        right := ratMid rect.left rect.right
        bottom := rect.bottom
        top := ratMid rect.bottom rect.top }
  | RectangleBranch.lowerRight =>
      { left := ratMid rect.left rect.right
        right := rect.right
        bottom := rect.bottom
        top := ratMid rect.bottom rect.top }
  | RectangleBranch.upperLeft =>
      { left := rect.left
        right := ratMid rect.left rect.right
        bottom := ratMid rect.bottom rect.top
        top := rect.top }
  | RectangleBranch.upperRight =>
      { left := ratMid rect.left rect.right
        right := rect.right
        bottom := ratMid rect.bottom rect.top
        top := rect.top }

def bisectionTraceRect : RationalRectangle -> List RectangleBranch ->
    RationalRectangle
  | rect, [] => rect
  | rect, branch :: rest =>
      bisectionTraceRect (bisectRectangle rect branch) rest

theorem bisectionTraceRect_nil (rect : RationalRectangle) :
    bisectionTraceRect rect [] = rect := by
  rfl

theorem bisectionTraceRect_cons (rect : RationalRectangle)
    (branch : RectangleBranch) (rest : List RectangleBranch) :
    bisectionTraceRect rect (branch :: rest) =
      bisectionTraceRect (bisectRectangle rect branch) rest := by
  rfl

structure BisectionStep (parent : RationalRectangle) where
  branch : RectangleBranch
  childTrace : ContourTrace (bisectRectangle parent branch)
  criterion : WindingZeroCriterion childTrace
  positive : 0 < contourWindingCount childTrace

theorem bisection_step_locates_zero {parent : RationalRectangle}
    (step : BisectionStep parent) :
    ContainsLocatedZetaZero (bisectRectangle parent step.branch) := by
  exact positive_count_contains_located_zero step.criterion step.positive

inductive BisectionLocationChain :
    RationalRectangle -> RationalRectangle -> Type where
  | already {rect : RationalRectangle} :
      ContainsLocatedZetaZero rect -> BisectionLocationChain rect rect
  | one {parent : RationalRectangle} :
      (step : BisectionStep parent) ->
        BisectionLocationChain parent (bisectRectangle parent step.branch)
  | cons {parent final : RationalRectangle} :
      (step : BisectionStep parent) ->
        BisectionLocationChain (bisectRectangle parent step.branch) final ->
          BisectionLocationChain parent final

def BisectionLocationChain.finalContains
    {start final : RationalRectangle}
    (chain : BisectionLocationChain start final) :
    ContainsLocatedZetaZero final :=
  match chain with
  | BisectionLocationChain.already contains => contains
  | BisectionLocationChain.one step =>
      bisection_step_locates_zero step
  | BisectionLocationChain.cons _step tail =>
      BisectionLocationChain.finalContains tail

theorem bisection_chain_locates_zero
    {start final : RationalRectangle}
    (chain : BisectionLocationChain start final) :
    ContainsLocatedZetaZero final :=
  BisectionLocationChain.finalContains chain

end BEDC.Derived.RHRoute.ArgumentPrincipleUp
