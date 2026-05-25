import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ClosedBoundedIntervalNetMeshRefinementFusion
    (x : ClosedBoundedIntervalNetUp) :
    ∃ L M Q D Z F S R E H C P N meshRead rationalRead dyadicRead centerRead
        coverageRead streamRead regseqRead realRead refinedRoute : BHist,
      x = ClosedBoundedIntervalNetUp.mk L M Q D Z F S R E H C P N ∧
        closedBoundedIntervalNetFields x = [L, M, Q, D, Z, F, S, R, E, H, C, P, N] ∧
          Cont M D meshRead ∧ Cont meshRead Q rationalRead ∧
            Cont rationalRead D dyadicRead ∧ Cont dyadicRead Z centerRead ∧
              Cont centerRead F coverageRead ∧ Cont coverageRead S streamRead ∧
                Cont streamRead R regseqRead ∧ Cont regseqRead E realRead ∧
                  Cont realRead C refinedRoute := by
  -- BEDC touchpoint anchor: BHist Cont append ClosedBoundedIntervalNetUp
  cases x with
  | mk L M Q D Z F S R E H C P N =>
      exact
        ⟨L, M, Q, D, Z, F, S, R, E, H, C, P, N,
          append M D,
          append (append M D) Q,
          append (append (append M D) Q) D,
          append (append (append (append M D) Q) D) Z,
          append (append (append (append (append M D) Q) D) Z) F,
          append (append (append (append (append (append M D) Q) D) Z) F) S,
          append (append (append (append (append (append (append M D) Q) D) Z) F) S) R,
          append
            (append (append (append (append (append (append (append M D) Q) D) Z) F) S) R)
            E,
          append
            (append
              (append
                (append (append (append (append (append (append M D) Q) D) Z) F) S)
                R)
              E)
            C,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.ClosedBoundedIntervalNetUp
