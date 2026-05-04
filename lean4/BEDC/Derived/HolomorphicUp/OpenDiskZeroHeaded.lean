import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem OpenDisk_zero_headed_component_absurd {z0 r z : BHist} :
    OpenDisk z0 r z ->
      ((∃ w : BHist, z0 = BHist.e0 w) ∨ (∃ w : BHist, r = BHist.e0 w) ∨
        (∃ w : BHist, z = BHist.e0 w)) -> False := by
  intro disk zeroComponent
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier _gapWitness =>
              cases zeroComponent with
              | inl centerZero =>
                  cases centerZero with
                  | intro w centerEq =>
                      cases centerEq
                      exact
                        (ComplexHistoryClassifier_e0_endpoint_absurd
                          (tail := w) (h := BHist.e0 w)).left
                          (And.intro centerCarrier
                            (And.intro centerCarrier (hsame_refl (BHist.e0 w))))
              | inr rest =>
                  cases rest with
                  | inl radiusZero =>
                      cases radiusZero with
                      | intro w radiusEq =>
                          cases radiusEq
                          exact unary_no_zero_extension radiusCarrier
                  | inr pointZero =>
                      cases pointZero with
                      | intro w pointEq =>
                          cases pointEq
                          exact
                            (ComplexHistoryClassifier_e0_endpoint_absurd
                              (tail := w) (h := BHist.e0 w)).left
                              (And.intro pointCarrier
                                (And.intro pointCarrier (hsame_refl (BHist.e0 w))))

end BEDC.Derived.HolomorphicUp
