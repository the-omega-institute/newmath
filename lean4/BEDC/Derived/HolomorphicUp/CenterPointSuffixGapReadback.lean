import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem HolomorphicOpenDiskWitnessed_center_point_unary_suffix_gap_public_readback
    {center radius point q centerq pointq radiusq : BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> UnaryHistory q ->
      Cont center q centerq -> Cont point q pointq -> Cont radius q radiusq ->
        HolomorphicOpenDiskWitnessed centerq radiusq pointq ∧
          (forall {displayedGap : BHist}, HolomorphicOpenDisk centerq radiusq pointq displayedGap ->
            ∃ gap : BHist, UnaryHistory gap ∧ Cont point gap radius ∧
              Cont pointq gap radiusq ∧ hsame gap displayedGap) := by
  intro disk suffixCarrier centerSuffix pointSuffix radiusSuffix
  constructor
  · exact
      (HolomorphicOpenDiskWitnessed_center_point_unary_suffix_transport disk suffixCarrier
        centerSuffix pointSuffix radiusSuffix).left
  · intro displayedGap displayed
    cases disk with
    | intro centerCarrier diskRest =>
        cases diskRest with
        | intro radiusCarrier diskRest =>
            cases diskRest with
            | intro pointCarrier gapWitness =>
                cases gapWitness with
                | intro gap gapData =>
                    cases gapData with
                    | intro gapCarrier pointGap =>
                        have gapDisk : HolomorphicOpenDiskGap center radius point gap :=
                          And.intro centerCarrier
                            (And.intro radiusCarrier
                              (And.intro pointCarrier (And.intro gapCarrier pointGap)))
                        have shifted :=
                          HolomorphicOpenDiskGap_unary_suffix_transport gapDisk suffixCarrier
                            pointSuffix radiusSuffix
                        exact Exists.intro gap
                          (And.intro gapCarrier
                            (And.intro pointGap
                              (And.intro shifted.right
                                (cont_left_cancel shifted.right
                                  displayed.right.right.right.right))))

end BEDC.Derived.HolomorphicUp
