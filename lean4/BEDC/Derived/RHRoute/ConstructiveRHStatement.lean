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

-- `ConstructiveRH` 是 RH 的构造性可陈述 surrogate: located 零点谓词接几何临界线。
-- `ConstructiveRH ↔ 经典 RH` 属于经典等价边界, 本文件只给出良构陈述与读回。
-- 这里绝不证明 `ConstructiveRH`; 该命题本身仍按开放问题处理。
def ConstructiveRH : Prop :=
  ∀ s : RatComplex, NontrivialZetaZero s -> OnCriticalLine s

end BEDC.Derived.RHRoute.ConstructiveRHStatement
