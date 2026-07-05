import BEDC.Derived.CompilerCompositionTraceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CompilerCompositionTraceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def CompilerCompositionTraceCarrier (_S M _T KSM KMT J G L H C _A _P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  Cont KSM KMT G ∧ Cont G L C ∧ hsame J M ∧ hsame H H ∧ hsame N N

theorem CompilerCompositionTraceCarrier_composite_replay
    {S M T KSM KMT J G L H C A P N : BHist} :
    CompilerCompositionTraceCarrier S M T KSM KMT J G L H C A P N →
      Cont KSM (append KMT L) C ∧ hsame J M ∧ hsame H H ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier
  obtain ⟨firstGraph, secondGraph, middleSame, sameH, sameN⟩ := carrier
  constructor
  · cases firstGraph
    cases secondGraph
    exact cont_intro (append_assoc KSM KMT L)
  · exact ⟨middleSame, sameH, sameN⟩

end BEDC.Derived.CompilerCompositionTraceUp
