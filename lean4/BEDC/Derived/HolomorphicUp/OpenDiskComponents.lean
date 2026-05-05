import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem OpenDisk_unary_components {z0 r z : BHist} :
    OpenDisk z0 r z ->
      UnaryHistory z0 ∧ UnaryHistory r ∧ UnaryHistory z ∧
        ∃ gap : BHist, UnaryHistory gap ∧ Cont gap z r := by
  intro disk
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier gapWitness =>
              exact
                And.intro (ComplexHistoryCarrier_unary centerCarrier)
                  (And.intro radiusCarrier
                    (And.intro (ComplexHistoryCarrier_unary pointCarrier) gapWitness))

end BEDC.Derived.HolomorphicUp
