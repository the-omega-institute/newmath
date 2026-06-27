import BEDC.Derived.RHRoute.FunctionalEquationSymmetry
import BEDC.Derived.RHRoute.ZeroGenerationInitiality
import BEDC.Derived.RHRoute.ZetaZeroLocated

namespace BEDC.Derived.RHRoute.ZeroFibreNormalSheet

open BEDC.Derived.RHRoute.FunctionalEquationSymmetry
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.ZetaZeroLocated

-- sheet 在这里是可判读的谓词层, 不声明解析流形、维度或谱几何。
structure ZeroFibre {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  zero : GeneratedZero signature
  point : SourceZeroPoint
  same_source : ComplexEq (epsilon zero) point

def NormalSheet {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (fibre : ZeroFibre epsilon) : Prop :=
  CriticalLine fibre.point

def FixedHalfSheet {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (fibre : ZeroFibre epsilon) : Prop :=
  SourceFixedHalf fibre.point

structure ZeroFibreNormalSheet {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  fibre : ZeroFibre epsilon
  normal : NormalSheet fibre

structure FixedHalfZeroFibreSheet {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  fibre : ZeroFibre epsilon
  fixed : FixedHalfSheet fibre

theorem normalSheet_iff_fixedHalfSheet {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (fibre : ZeroFibre epsilon) :
    NormalSheet fibre ↔ FixedHalfSheet fibre := by
  constructor
  · intro normal
    exact (criticalLine_J_fixed_iff fibre.point).mpr normal
  · intro fixed
    exact (criticalLine_J_fixed_iff fibre.point).mp fixed

def normalSheetToFixedHalfSheet {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (sheet : ZeroFibreNormalSheet epsilon) :
    FixedHalfZeroFibreSheet epsilon :=
  { fibre := sheet.fibre
    fixed := (normalSheet_iff_fixedHalfSheet sheet.fibre).mp sheet.normal }

def fixedHalfSheetToNormalSheet {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (sheet : FixedHalfZeroFibreSheet epsilon) :
    ZeroFibreNormalSheet epsilon :=
  { fibre := sheet.fibre
    normal := (normalSheet_iff_fixedHalfSheet sheet.fibre).mpr sheet.fixed }

def zeroFibreOfGenerated {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint)
    (zero : GeneratedZero signature) : ZeroFibre epsilon :=
  { zero := zero
    point := epsilon zero
    same_source := ComplexEq_refl (epsilon zero) }

def fixedHalfSheetOfGenerated {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    FixedHalfZeroFibreSheet epsilon :=
  { fibre := zeroFibreOfGenerated epsilon zero
    fixed := generatedFixedHalfWitness closed zero }

def normalSheetOfGenerated {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    ZeroFibreNormalSheet epsilon :=
  fixedHalfSheetToNormalSheet (fixedHalfSheetOfGenerated closed zero)

theorem normalSheetOfGenerated_point {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    (normalSheetOfGenerated closed zero).fibre.point = epsilon zero := by
  rfl

theorem normalSheetOfGenerated_zero {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    (normalSheetOfGenerated closed zero).fibre.zero = zero := by
  rfl

theorem fixedHalfSheetOfGenerated_kernel {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    FixedHalfSheet (fixedHalfSheetOfGenerated closed zero).fibre :=
  generatedFixedHalfWitness closed zero

theorem normalSheetOfGenerated_kernel {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (zero : GeneratedZero signature) :
    NormalSheet (normalSheetOfGenerated closed zero).fibre :=
  generatedFixedHalf_criticalLine closed zero

structure LocatedZeroFibre where
  point : RatComplex
  zero : ZetaZeroLocated point

def LocatedNormalSheet (fibre : LocatedZeroFibre) : Prop :=
  CriticalLineLocated fibre.point

def LocatedFunctionalNormalSheet (fibre : LocatedZeroFibre) : Prop :=
  CriticalLine (functionalSymmetryPointOfRatComplex fibre.point)

def LocatedFixedHalfSheet (fibre : LocatedZeroFibre) : Prop :=
  JFixed (functionalSymmetryPointOfRatComplex fibre.point)

theorem locatedNormalSheet_to_functionalNormalSheet
    (fibre : LocatedZeroFibre) :
    LocatedNormalSheet fibre -> LocatedFunctionalNormalSheet fibre := by
  intro normal
  exact CriticalLineLocated_to_FunctionalEquationSymmetry fibre.point normal

theorem locatedFunctionalNormalSheet_iff_fixedHalfSheet
    (fibre : LocatedZeroFibre) :
    LocatedFunctionalNormalSheet fibre ↔ LocatedFixedHalfSheet fibre := by
  constructor
  · intro normal
    exact
      (criticalLine_J_fixed_iff
        (functionalSymmetryPointOfRatComplex fibre.point)).mpr normal
  · intro fixed
    exact
      (criticalLine_J_fixed_iff
        (functionalSymmetryPointOfRatComplex fibre.point)).mp fixed

theorem locatedNormalSheet_to_fixedHalfSheet
    (fibre : LocatedZeroFibre) :
    LocatedNormalSheet fibre -> LocatedFixedHalfSheet fibre := by
  intro normal
  exact (locatedFunctionalNormalSheet_iff_fixedHalfSheet fibre).mp
    (locatedNormalSheet_to_functionalNormalSheet fibre normal)

end BEDC.Derived.RHRoute.ZeroFibreNormalSheet
