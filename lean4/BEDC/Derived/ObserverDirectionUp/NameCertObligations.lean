import BEDC.Derived.ObserverDirectionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ObserverDirectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

theorem ObserverDirectionUp_namecert_obligations (x : ObserverDirectionUp) :
    ∃ R T U L B H C P N : BHist,
      x = ObserverDirectionUp.mk R T U L B H C P N ∧
        FieldFaithful.fields x = [R, T, U, L, B, H, C, P, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            Cont C P (append C P) ∧ hsame (append C P) (append C P) ∧
              observerDirectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful BHistCarrier
  cases x with
  | mk R T U L B H C P N =>
      exact
        ⟨R, T, U, L, B, H, C, P, N, rfl, rfl,
          ChapterTasteGate.round_trip (ObserverDirectionUp.mk R T U L B H C P N),
          rfl, hsame_refl (append C P), rfl⟩

end BEDC.Derived.ObserverDirectionUp
