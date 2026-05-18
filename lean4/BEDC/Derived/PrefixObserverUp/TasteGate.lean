import BEDC.Derived.PrefixObserverUp

namespace BEDC.Derived.PrefixObserverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem PrefixObserverNameCert_obligations :
    (∀ x : PrefixObserverUp,
      ∃ S W R K U L H C Q N : BHist,
        x = PrefixObserverUp.mk S W R K U L H C Q N ∧
          FieldFaithful.fields x = [S, W, R, K, U, L, H, C, Q, N]) ∧
      (∀ S W R K U L H C Q N : BHist,
        BHistCarrier.toEventFlow (PrefixObserverUp.mk S W R K U L H C Q N) =
          prefixObserverToEventFlow (PrefixObserverUp.mk S W R K U L H C Q N)) ∧
        prefixObserverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · intro x
    cases x with
    | mk S W R K U L H C Q N =>
        exact ⟨S, W, R, K, U, L, H, C, Q, N, rfl, rfl⟩
  · constructor
    · intro S W R K U L H C Q N
      rfl
    · rfl

end BEDC.Derived.PrefixObserverUp
