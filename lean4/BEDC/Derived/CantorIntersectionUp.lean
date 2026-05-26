import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive CantorIntersectionCarrier where
  | packet
      (nestedIntersection widthWindow diagonalSelector endpointEnclosure regSeqRatHandoff
        realSeal transport package nameCert : BHist) :
      CantorIntersectionCarrier

structure CantorIntersectionCarrier_namecert_obligations where
  carrier : CantorIntersectionCarrier -> Prop
  finiteWindowClassifier : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  selectorStability : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  regSeqRatHandoffExactness : CantorIntersectionCarrier -> Prop
  realSealNonescape : CantorIntersectionCarrier -> Prop

theorem CantorIntersectionRealSealNonescape (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q selectedWindow selectedEndpoint regSeqRead realRead replay : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont W D selectedWindow ∧
          Cont selectedWindow E selectedEndpoint ∧
            Cont selectedEndpoint R regSeqRead ∧
              Cont regSeqRead H realRead ∧
                Cont C P replay ∧ hsame realRead (append regSeqRead H) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact
        ⟨N, W, D, E, R, H, C, P, Q,
          append W D,
          append (append W D) E,
          append (append (append W D) E) R,
          append (append (append (append W D) E) R) H,
          append C P,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CantorIntersectionUp
