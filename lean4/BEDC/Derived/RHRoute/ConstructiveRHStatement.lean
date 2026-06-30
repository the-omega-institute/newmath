import BEDC.Derived.RHRoute.ZetaZeroLocated
import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.ConstructiveRHStatement

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete
open BEDC.Derived.RHRoute.ZetaZeroLocated

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ZetaBoxEvaluator.RatComplex

def RatComplexEq (z w : RatComplex) : Prop :=
  RatEq z.re w.re ∧ RatEq z.im w.im

def zetaPolePoint : RatComplex :=
  ratComplexOne

def negativeEvenIntegerOnRealAxis (n : Nat) : RatComplex :=
  { re := ratNeg (concreteNatRat (Nat.succ (Nat.succ (n + n))))
    im := ratZero }

def InCriticalStrip (s : RatComplex) : Prop :=
  ratLe ratZero s.re ∧ ratLe s.re ratOne

def TrivialZero (s : RatComplex) : Prop :=
  ∃ n : Nat, RatComplexEq s (negativeEvenIntegerOnRealAxis n)

-- `NontrivialZetaZero` is scoped to the located `RatComplex` box surface:
-- `ZetaZeroLocated` reads the concrete zeta boxes built from rational input
-- data.  That surface is partial-computational; it does not consume the
-- functional equation, analytic continuation, or Euler product as proof data.
def NontrivialZetaZero (s : RatComplex) : Prop :=
  ZetaZeroLocated s ∧ InCriticalStrip s ∧ Not (TrivialZero s) ∧
    Not (RatComplexEq s zetaPolePoint)

def OnCriticalLine (s : RatComplex) : Prop :=
  CriticalLineLocated s

def OnCriticalLineSymmetryReadback (s : RatComplex) : Prop :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
    (functionalSymmetryPointOfRatComplex s)

def OnCriticalLineJFixedReadback (s : RatComplex) : Prop :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.JFixed
    (functionalSymmetryPointOfRatComplex s)

theorem onCriticalLine_to_functionalSymmetry (s : RatComplex) :
    OnCriticalLine s -> OnCriticalLineSymmetryReadback s := by
  intro h
  exact CriticalLineLocated_to_FunctionalEquationSymmetry s h

theorem onCriticalLine_to_JFixed (s : RatComplex) :
    OnCriticalLine s -> OnCriticalLineJFixedReadback s := by
  intro h
  exact
    (BEDC.Derived.RHRoute.FunctionalEquationSymmetry.criticalLine_J_fixed_iff
      (functionalSymmetryPointOfRatComplex s)).mpr
      (onCriticalLine_to_functionalSymmetry s h)

theorem onCriticalLine_reads_re_half (s : RatComplex) :
    OnCriticalLine s = RatEq s.re halfRat := by
  rfl

theorem generatedFixedHalf_reads_criticalLine
    {signature :
      BEDC.Derived.RHRoute.ZeroGenerationInitiality.RHFreeZeroSignature}
    {epsilon :
      BEDC.Derived.RHRoute.ZeroGenerationInitiality.GeneratedZero signature ->
        BEDC.Derived.RHRoute.ZeroGenerationInitiality.SourceZeroPoint}
    (closed :
      BEDC.Derived.RHRoute.ZeroGenerationInitiality.FixedHalfClosedZeroSignature
        epsilon)
    (z : BEDC.Derived.RHRoute.ZeroGenerationInitiality.GeneratedZero
      signature) :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
      (epsilon z) :=
  BEDC.Derived.RHRoute.ZeroGenerationInitiality.generatedFixedHalf_criticalLine
    closed z

-- `ConstructiveRH` is a located, `RatComplex`-coded RH-shaped proposition:
-- the quantifier ranges over rational complex points, not over the
-- regular-Cauchy `ComplexUp` histories used by the classical BEDC RH
-- predicate.  The bridge from `RatComplex` located zeros to `ComplexUp` zeros,
-- and from located equality to the classical reading, is boundary work shared
-- with the located-real convergence foundation.  This definition does not
-- claim classical RH, and it does not claim a proof of RH.
def ConstructiveRH : Prop :=
  ∀ s : RatComplex, NontrivialZetaZero s -> OnCriticalLine s

end BEDC.Derived.RHRoute.ConstructiveRHStatement
