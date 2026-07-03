import BEDC.Derived.KernelObservationSieveUp.TasteGate

namespace BEDC.Derived.KernelObservationSieveUp

open BEDC.FKernel.Hist

theorem KernelObservationSieveRejectedLedger_nonescape (O S F A R T C P N : BHist) :
    ∃ K : KernelObservationSieveUp,
      K = KernelObservationSieveUp.mk O S F A R T C P N ∧
        ∀ {O' S' F' A' R' T' C' P' N' : BHist},
          K = KernelObservationSieveUp.mk O' S' F' A' R' T' C' P' N' → R' = R := by
  -- BEDC touchpoint anchor: BHist KernelObservationSieveUp
  refine ⟨KernelObservationSieveUp.mk O S F A R T C P N, rfl, ?_⟩
  intro O' S' F' A' R' T' C' P' N' displayed
  cases displayed
  rfl

end BEDC.Derived.KernelObservationSieveUp
