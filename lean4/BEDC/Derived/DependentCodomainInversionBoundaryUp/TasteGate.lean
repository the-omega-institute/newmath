import BEDC.Derived.DependentCodomainInversionBoundaryUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.DependentCodomainInversionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

def dependentCodomainInversionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dependentCodomainInversionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dependentCodomainInversionBoundaryEncodeBHist h

def dependentCodomainInversionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dependentCodomainInversionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dependentCodomainInversionBoundaryDecodeBHist tail)

private theorem DependentCodomainInversionBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dependentCodomainInversionBoundaryDecodeBHist
          (dependentCodomainInversionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dependentCodomainInversionBoundaryToEventFlow :
    DependentCodomainInversionBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (dependentCodomainInversionBoundaryFields x).map
      dependentCodomainInversionBoundaryEncodeBHist

theorem DependentCodomainInversionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        dependentCodomainInversionBoundaryDecodeBHist
            (dependentCodomainInversionBoundaryEncodeBHist h) =
          h) ∧
      (∀ Pi A a a' C0 C1 S R O H P N : BHist,
        dependentCodomainInversionBoundaryFields
            (DependentCodomainInversionBoundaryUp.mk Pi A a a' C0 C1 S R O H P N) =
          [Pi, A, a, a', C0, C1, S, R, O, H, append S R, P, N] ∧
          hsame H H ∧ Cont S R (append S R)) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  constructor
  · exact DependentCodomainInversionBoundaryTasteGate_single_carrier_alignment_decode_encode
  · intro Pi A a a' C0 C1 S R O H P N
    constructor
    · rfl
    · constructor
      · exact hsame_refl H
      · exact cont_intro rfl

end BEDC.Derived.DependentCodomainInversionBoundaryUp
