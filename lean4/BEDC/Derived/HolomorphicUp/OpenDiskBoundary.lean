import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem OpenDisk_empty_radius_boundary {z0 z : BHist} :
    OpenDisk z0 BHist.Empty z ->
      hsame z BHist.Empty ∧ ∃ gap : BHist,
        UnaryHistory gap ∧ hsame gap BHist.Empty ∧ Cont gap z BHist.Empty := by
  intro disk
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusUnary rest =>
          cases rest with
          | intro _pointCarrier gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  cases gapData with
                  | intro gapUnary gapCont =>
                      have endpoints := cont_empty_result_inversion gapCont
                      exact And.intro endpoints.right
                        (Exists.intro gap
                          (And.intro gapUnary (And.intro endpoints.left gapCont)))

theorem OpenDiskGap_e0_point_empty_radius_absurd {z0 z gap : BHist} :
    OpenDiskGap z0 BHist.Empty (BHist.e0 z) gap -> False := by
  intro disk
  have endpoints := cont_empty_result_inversion disk.right.right.right
  exact not_hsame_e0_empty endpoints.left

end BEDC.Derived.HolomorphicUp
