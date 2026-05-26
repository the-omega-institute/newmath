import BEDC.Derived.CantorIntersectionUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CantorIntersection_public_completion_consumer (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q nestedRead endpointRead regularRead realRead publicRoute : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont N W nestedRead ∧
          Cont D E endpointRead ∧
            Cont endpointRead R regularRead ∧
              Cont regularRead H realRead ∧
                Cont (append nestedRead endpointRead) (append regularRead H) publicRoute ∧
                  hsame publicRoute (append (append nestedRead endpointRead) (append regularRead H)) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact
        ⟨N, W, D, E, R, H, C, P, Q,
          append N W,
          append D E,
          append (append D E) R,
          append (append (append D E) R) H,
          append (append (append N W) (append D E)) (append (append (append D E) R) H),
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CantorIntersectionPublicCompletionConsumer (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q selectedWindow selectedEndpoint regSeqRead realRead publicRead :
      BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont W D selectedWindow ∧
          Cont selectedWindow E selectedEndpoint ∧
            Cont selectedEndpoint R regSeqRead ∧
              Cont regSeqRead H realRead ∧
                Cont realRead Q publicRead ∧
                  hsame publicRead (append realRead Q) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | packet N W D E R H C P Q =>
      exact
        ⟨N, W, D, E, R, H, C, P, Q,
          append W D,
          append (append W D) E,
          append (append (append W D) E) R,
          append (append (append (append W D) E) R) H,
          append (append (append (append (append W D) E) R) H) Q,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CantorIntersectionUp
