import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem HolomorphicStabilityCert_suffix_gap_comm {center radius point q pointq radiusq gap :
    BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> UnaryHistory q -> Cont point q pointq ->
      Cont radius q radiusq -> UnaryHistory gap -> Cont pointq gap radiusq ->
        HolomorphicOpenDiskWitnessed center radiusq pointq ∧ hsame radiusq (append gap pointq) := by
  intro disk suffixCarrier pointSuffix radiusSuffix gapCarrier shiftedGap
  have shifted :
      HolomorphicOpenDiskWitnessed center radiusq pointq ∧
        ∃ displayedGap : BHist, UnaryHistory displayedGap ∧ Cont pointq displayedGap radiusq :=
    HolomorphicOpenDiskWitnessed_unary_suffix_transport
      disk suffixCarrier pointSuffix radiusSuffix
  have displayedDisk : HolomorphicOpenDisk center radiusq pointq gap :=
    And.intro shifted.left.left
      (And.intro shifted.left.right.left
        (And.intro shifted.left.right.right.left
          (And.intro gapCarrier shiftedGap)))
  exact And.intro shifted.left (HolomorphicOpenDisk_gap_point_comm displayedDisk)

end BEDC.Derived.HolomorphicUp
