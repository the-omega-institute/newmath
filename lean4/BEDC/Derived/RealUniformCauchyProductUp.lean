import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.RealUniformCauchyProductUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive RealUniformCauchyProductUp : Type where
  | mk (F G M WF WG D U K R E H C Q N : BHist) : RealUniformCauchyProductUp

theorem RealUniformCauchyProductCarrier_namecert_obligations
    (x : RealUniformCauchyProductUp) :
    ∃ F G M WF WG D U K R E H C Q N : BHist,
      x = RealUniformCauchyProductUp.mk F G M WF WG D U K R E H C Q N ∧
        hsame F F ∧ Cont H C (append H C) ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | mk F G M WF WG D U K R E H C Q N =>
      exact ⟨F, G, M, WF, WG, D, U, K, R, E, H, C, Q, N, rfl, hsame_refl F, rfl,
        hsame_refl E⟩

end BEDC.Derived.RealUniformCauchyProductUp
