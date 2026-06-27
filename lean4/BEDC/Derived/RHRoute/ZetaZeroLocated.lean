import BEDC.Derived.RHRoute.BoxKernelConcrete
import BEDC.Derived.RHRoute.FunctionalEquationSymmetry

namespace BEDC.Derived.RHRoute.ZetaZeroLocated

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete

abbrev Rat : Type :=
  RatNum

def complexZero : RatComplex :=
  ratComplexZero

def RatInInterval (q : Rat) (I : QInterval) : Prop :=
  ratLe I.lo q ∧ ratLe q I.hi

def ComplexInBox (z : RatComplex) (box : ComplexBox) : Prop :=
  RatInInterval z.re box.re ∧ RatInInterval z.im box.im

def ComplexBoxExcludesZero (box : ComplexBox) : Prop :=
  ComplexInBox complexZero box -> False

private theorem intLt_not_intLe_reverse {x y : RatInt} :
    intLtUp x y -> intLe y x -> False := by
  intro hlt hle
  unfold intLtUp at hlt
  unfold intLe at hle
  have hleLen := (BEDC.Derived.IntUp.pairLe_iff_length_order
    (intToPair_carrier y) (intToPair_carrier x)).mp hle
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hleLen)

theorem ratLt_not_ratLe_reverse {x y : Rat} :
    ratLt x y -> ratLe y x -> False := by
  intro hlt hle
  unfold ratLt at hlt
  unfold ratLe at hle
  exact intLt_not_intLe_reverse hlt hle

theorem complexBoxExcludesZero_of_re_lo_pos {box : ComplexBox} :
    ratLt ratZero box.re.lo -> ComplexBoxExcludesZero box := by
  intro pos contains
  exact ratLt_not_ratLe_reverse pos contains.left.left

def concreteZetaEvaluatorFromCriticalStrip
    (s : CriticalStripInput)
    (denominator : DenominatorSeparation s concreteBoxGauge)
    (division :
      ZetaDivisionCertificate concreteBoxGauge denominator.denominatorCenter
        denominator.denominator_apart) :
    ZetaBoxEvaluator concreteBoxGauge s :=
  { kernel := locatedTaylorComplexApproxKernel (criticalStripPoint s)
    boxAdd := concreteBoxAddCertificate
    etaPairTerm := concreteEtaPairTermCertificate (criticalStripPoint s)
    etaTail := concreteEtaTailCertificate (criticalStripPoint s)
    denominator := denominator
    division := division }

def concreteZetaBoxAt
    (s : CriticalStripInput)
    (denominator : DenominatorSeparation s concreteBoxGauge)
    (division :
      ZetaDivisionCertificate concreteBoxGauge denominator.denominatorCenter
        denominator.denominator_apart)
    (precision : Nat) : ComplexBox :=
  zetaBox (concreteZetaEvaluatorFromCriticalStrip s denominator division) precision

theorem concreteZetaBoxAt_fits
    (s : CriticalStripInput)
    (denominator : DenominatorSeparation s concreteBoxGauge)
    (division :
      ZetaDivisionCertificate concreteBoxGauge denominator.denominatorCenter
        denominator.denominator_apart)
    (precision : Nat) :
    concreteBoxGauge.fits
      (concreteZetaBoxAt s denominator division precision) precision := by
  exact zetaBox_fits
    (concreteZetaEvaluatorFromCriticalStrip s denominator division) precision

structure ConcreteZetaLocatedInput where
  point : RatComplex
  strip : CriticalStripInput
  point_eq : criticalStripPoint strip = point
  denominator : DenominatorSeparation strip concreteBoxGauge
  division :
    ZetaDivisionCertificate concreteBoxGauge denominator.denominatorCenter
      denominator.denominator_apart

def ConcreteZetaLocatedInput.evaluator
    (input : ConcreteZetaLocatedInput) :
    ZetaBoxEvaluator concreteBoxGauge input.strip :=
  concreteZetaEvaluatorFromCriticalStrip input.strip input.denominator input.division

def concreteZetaBox (input : ConcreteZetaLocatedInput)
    (precision : Nat) : ComplexBox :=
  zetaBox input.evaluator precision

theorem concreteZetaBox_fits (input : ConcreteZetaLocatedInput)
    (precision : Nat) :
    concreteBoxGauge.fits (concreteZetaBox input precision) precision := by
  exact zetaBox_fits input.evaluator precision

def criticalHalfConcreteInput : ConcreteZetaLocatedInput :=
  { point := criticalStripPoint concreteCriticalStripHalf
    strip := concreteCriticalStripHalf
    point_eq := rfl
    denominator := criticalHalfDenominatorSeparation
    division := criticalHalfDivisionCertificate }

def criticalHalfConcreteZetaBox (precision : Nat) : ComplexBox :=
  concreteZetaBoxAt concreteCriticalStripHalf criticalHalfDenominatorSeparation
    criticalHalfDivisionCertificate precision

theorem criticalHalfConcreteZetaBox_readback (precision : Nat) :
    criticalHalfConcreteZetaBox precision =
      BEDC.Derived.RHRoute.BoxKernelConcrete.concreteZetaBox precision := by
  rfl

def ZetaZeroLocated (s : RatComplex) : Prop :=
  ∃ input : ConcreteZetaLocatedInput,
    input.point = s ∧
      ∀ precision : Nat,
        ComplexInBox complexZero (concreteZetaBox input precision)

def ZetaNonzeroLocated (s : RatComplex) : Prop :=
  ∃ input : ConcreteZetaLocatedInput,
    input.point = s ∧
      ∃ precision : Nat,
        ComplexBoxExcludesZero (concreteZetaBox input precision)

structure ZetaNonzeroWitness (s : RatComplex)
    (input : ConcreteZetaLocatedInput) where
  point_eq : input.point = s
  precision : Nat
  excludes_zero :
    ComplexBoxExcludesZero (concreteZetaBox input precision)

def zetaNonzeroWitnessToLocated {s : RatComplex}
    {input : ConcreteZetaLocatedInput}
    (w : ZetaNonzeroWitness s input) : ZetaNonzeroLocated s :=
  Exists.intro input
    (And.intro w.point_eq (Exists.intro w.precision w.excludes_zero))

def criticalHalfPoint : RatComplex :=
  criticalStripPoint concreteCriticalStripHalf

theorem criticalHalfConcreteZetaBox_fits (precision : Nat) :
    concreteBoxGauge.fits (criticalHalfConcreteZetaBox precision) precision := by
  exact concreteZetaBoxAt_fits concreteCriticalStripHalf
    criticalHalfDenominatorSeparation criticalHalfDivisionCertificate precision

theorem criticalHalfConcreteZetaBox_zero_readback :
    criticalHalfConcreteZetaBox 0 =
      BEDC.Derived.RHRoute.BoxKernelConcrete.concreteZetaBox 0 := by
  rfl

theorem criticalHalfConcreteZetaBox_zero_value :
    concreteZetaBox criticalHalfConcreteInput 0 =
      pointBox
        (ratComplexDivApart
          (boxCenter
            (etaPairPartialSumBox concreteBoxAddCertificate
              (concreteEtaPairTermCertificate criticalHalfPoint) 1 0))
          criticalHalfDenominatorCenter criticalHalfDenominator_apart) := by
  rfl

theorem criticalHalfConcreteInput_point :
    criticalHalfConcreteInput.point = criticalHalfPoint := by
  rfl

theorem criticalHalfConcreteInput_zetaBox_readback (precision : Nat) :
    concreteZetaBox criticalHalfConcreteInput precision =
      criticalHalfConcreteZetaBox precision := by
  rfl

def zetaTwoPoint : RatComplex :=
  rationalTwoOnRealAxis

def concreteZetaTwoBoxForLocatedZero (precision : Nat) : ComplexBox :=
  let _kernel := locatedTaylorComplexApproxKernel zetaTwoPoint
  concreteZetaTwoBox precision

theorem concreteZetaTwoBoxForLocatedZero_readback (precision : Nat) :
    concreteZetaTwoBoxForLocatedZero precision =
      concreteZetaTwoBox precision := by
  rfl

theorem concreteZetaTwoBoxForLocatedZero_fits (precision : Nat) :
    concreteBoxGauge.fits
      (concreteZetaTwoBoxForLocatedZero precision) precision := by
  unfold concreteZetaTwoBoxForLocatedZero
  exact concreteZetaTwoBox_fits precision

def CriticalLineLocated (s : RatComplex) : Prop :=
  RatEq s.re halfRat

def functionalSymmetryPointOfRatComplex (s : RatComplex) :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.RationalComplex :=
  { reAboveHalf := s.re
    reBelowHalf := halfRat
    im := BEDC.Derived.RHRoute.FunctionalEquationSymmetry.signedRatZero }

theorem CriticalLineLocated_to_FunctionalEquationSymmetry
    (s : RatComplex) :
    CriticalLineLocated s ->
      BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
        (functionalSymmetryPointOfRatComplex s) := by
  intro h
  exact h

theorem criticalHalfPoint_on_critical_line :
    CriticalLineLocated criticalHalfPoint := by
  exact RatEq_refl halfRat

theorem criticalHalfPoint_functional_symmetry :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
      (functionalSymmetryPointOfRatComplex criticalHalfPoint) := by
  exact CriticalLineLocated_to_FunctionalEquationSymmetry criticalHalfPoint
    criticalHalfPoint_on_critical_line

def zetaNonzeroWitnessOfExclusion {s : RatComplex}
    {input : ConcreteZetaLocatedInput}
    (point_eq : input.point = s)
    (precision : Nat)
    (excludes_zero : ComplexBoxExcludesZero (concreteZetaBox input precision)) :
    ZetaNonzeroWitness s input :=
  { point_eq := point_eq
    precision := precision
    excludes_zero := excludes_zero }

theorem zetaZeroLocated_at {s : RatComplex}
    (h : ZetaZeroLocated s) (precision : Nat) :
    ∃ input : ConcreteZetaLocatedInput,
      input.point = s ∧
        ComplexInBox complexZero (concreteZetaBox input precision) := by
  cases h with
  | intro input data =>
      exact Exists.intro input
        (And.intro data.left (data.right precision))

theorem zetaNonzeroLocated_precision {s : RatComplex}
    (h : ZetaNonzeroLocated s) :
    ∃ input : ConcreteZetaLocatedInput,
      input.point = s ∧
        ∃ precision : Nat,
          ComplexBoxExcludesZero (concreteZetaBox input precision) :=
  h

end BEDC.Derived.RHRoute.ZetaZeroLocated
