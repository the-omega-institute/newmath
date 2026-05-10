import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def HolomorphicStabilityCert (center radius point : BHist) : Prop :=
  HolomorphicOpenDiskWitnessed center radius point ∧
    (forall {center' radius' point' : BHist},
      hsame center center' -> hsame radius radius' -> hsame point point' ->
        HolomorphicOpenDiskWitnessed center' radius' point')

theorem HolomorphicStabilityCert_openDisk_transport_fields
    {center center' radius radius' point point' : BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> hsame center center' ->
      hsame radius radius' -> hsame point point' ->
        HolomorphicStabilityCert center radius point ∧
          HolomorphicOpenDiskWitnessed center' radius' point' ∧
            UnaryHistory center' ∧ UnaryHistory radius' ∧ UnaryHistory point' := by
  intro disk sameCenter sameRadius samePoint
  have transported :
      HolomorphicOpenDiskWitnessed center' radius' point' ∧
        ∃ gap : BHist, UnaryHistory gap ∧ Cont point' gap radius' :=
    HolomorphicOpenDiskWitnessed_boundary_hsame_transport disk sameCenter sameRadius samePoint
  have stability : HolomorphicStabilityCert center radius point :=
    And.intro disk
      (by
        intro center'' radius'' point'' sameCenter'' sameRadius'' samePoint''
        exact (HolomorphicOpenDiskWitnessed_boundary_hsame_transport disk sameCenter''
          sameRadius'' samePoint'').left)
  exact And.intro stability
    (And.intro transported.left
      (And.intro transported.left.left
        (And.intro transported.left.right.left transported.left.right.right.left)))

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
