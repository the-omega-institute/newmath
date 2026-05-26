import BEDC.Derived.CantorIntersectionUp

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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
