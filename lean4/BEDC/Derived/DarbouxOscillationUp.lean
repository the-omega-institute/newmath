import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive DarbouxOscillationUp : Type where
  | mk
      (partition mesh upper lower oscillation realSeal transport replay provenance name : BHist) :
      DarbouxOscillationUp
  deriving DecidableEq

namespace DarbouxOscillationUp

theorem DarbouxOscillationCarrier_refinement_bound (O : DarbouxOscillationUp) :
    ∃ partition mesh upper lower oscillation realSeal transport replay provenance name
      meshReplay oscillationReplay : BHist,
      O =
          DarbouxOscillationUp.mk partition mesh upper lower oscillation realSeal transport replay
            provenance name ∧
        Cont partition mesh meshReplay ∧
        Cont upper lower oscillationReplay ∧
        hsame oscillation oscillation ∧ hsame realSeal realSeal := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases O with
  | mk partition mesh upper lower oscillation realSeal transport replay provenance name =>
      exact
        ⟨partition, mesh, upper, lower, oscillation, realSeal, transport, replay, provenance,
          name, append partition mesh, append upper lower, rfl, rfl, rfl, hsame_refl oscillation,
          hsame_refl realSeal⟩

end DarbouxOscillationUp

end BEDC.Derived
