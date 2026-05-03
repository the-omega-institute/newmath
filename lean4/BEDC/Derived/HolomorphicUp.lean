import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp
import BEDC.Derived.NatUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.NatUp

def HolomorphicOpenDisk (center radius point gap : BHist) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory point ∧ UnaryHistory gap ∧
    Cont point gap radius

theorem HolomorphicOpenDisk_hsame_transport {center center' radius radius' point point' gap gap' :
    BHist} :
    hsame center center' -> hsame radius radius' -> hsame point point' -> hsame gap gap' ->
      HolomorphicOpenDisk center radius point gap ->
        HolomorphicOpenDisk center' radius' point' gap' ∧ UnaryHistory center' ∧
          UnaryHistory radius' ∧ UnaryHistory point' ∧ UnaryHistory gap' ∧
            Cont point' gap' radius' := by
  intro sameCenter sameRadius samePoint sameGap disk
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier ledger =>
                  have centerCarrier' : UnaryHistory center' :=
                    unary_transport centerCarrier sameCenter
                  have radiusCarrier' : UnaryHistory radius' :=
                    unary_transport radiusCarrier sameRadius
                  have pointCarrier' : UnaryHistory point' :=
                    unary_transport pointCarrier samePoint
                  have gapCarrier' : UnaryHistory gap' :=
                    unary_transport gapCarrier sameGap
                  have ledger' : Cont point' gap' radius' :=
                    cont_hsame_transport samePoint sameGap sameRadius ledger
                  exact And.intro
                    (And.intro centerCarrier'
                      (And.intro radiusCarrier'
                        (And.intro pointCarrier'
                          (And.intro gapCarrier' ledger'))))
                    (And.intro centerCarrier'
                      (And.intro radiusCarrier'
                        (And.intro pointCarrier'
                          (And.intro gapCarrier' ledger'))))

theorem HolomorphicOpenDisk_radius_extension_closed {center radius radius' point gap extra :
    BHist} :
    HolomorphicOpenDisk center radius point gap -> UnaryHistory extra ->
      Cont radius extra radius' -> HolomorphicOpenDisk center radius' point (append gap extra) := by
  intro disk extraCarrier radiusStep
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have radiusCarrier' : UnaryHistory radius' :=
                    unary_cont_closed radiusCarrier extraCarrier radiusStep
                  have extendedGapCarrier : UnaryHistory (append gap extra) :=
                    unary_append_closed gapCarrier extraCarrier
                  have extendedLedger : Cont point (append gap extra) radius' := by
                    cases pointGap
                    exact radiusStep.trans (append_assoc point gap extra)
                  exact And.intro centerCarrier
                    (And.intro radiusCarrier'
                      (And.intro pointCarrier
                        (And.intro extendedGapCarrier extendedLedger)))

theorem HolomorphicOpenDisk_e1_gap_radius_inversion {z0 z gap radius : BHist} :
    ComplexHistoryCarrier z0 -> ComplexHistoryCarrier z -> UnaryHistory gap ->
      NatUnaryStrictPrefix (BHist.e1 gap) (BHist.e1 radius) -> Cont z0 (BHist.e1 gap) z ->
        NatUnaryStrictPrefix z0 z ∧ NatUnaryStrictPrefix gap radius := by
  intro _centerCarrier _pointCarrier gapUnary radiusStrict centerToPoint
  constructor
  · exact ⟨BHist.e1 gap, unary_e1_closed gapUnary, (fun empty => by cases empty), centerToPoint⟩
  · exact NatUnaryStrictPrefix_e1_inversion radiusStrict

def HolomorphicOpenDiskCarrier (center radius point : BHist) : Prop :=
  BEDC.Derived.ComplexUp.ComplexHistoryCarrier center ∧
    BEDC.Derived.RatUp.RatHistoryCarrier radius ∧
      BEDC.Derived.ComplexUp.ComplexHistoryCarrier point ∧
        ∃ gap : BHist, UnaryHistory gap ∧ NatUnaryStrictPrefix gap radius ∧
          Cont point gap radius

def HolomorphicOpenDiskWitnessed (center radius point : BHist) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory point ∧
    ∃ gap : BHist, UnaryHistory gap ∧ Cont point gap radius

theorem HolomorphicOpenDisk_radius_extension_gap_witness
    {center point radius extra radius' : BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> UnaryHistory extra ->
      Cont radius extra radius' ->
        ∃ gap : BHist, ∃ extendedGap : BHist,
          UnaryHistory gap ∧ UnaryHistory extendedGap ∧ Cont point gap radius ∧
            Cont gap extra extendedGap ∧ Cont point extendedGap radius' := by
  intro disk extraUnary radiusExtension
  cases disk with
  | intro _centerUnary diskRest =>
      cases diskRest with
      | intro _radiusUnary diskRest =>
          cases diskRest with
          | intro _pointUnary gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  cases gapData with
                  | intro gapUnary pointGap =>
                      have middle := cont_assoc_middle_exists pointGap radiusExtension
                      cases middle with
                      | intro extendedGap extendedData =>
                          cases extendedData with
                          | intro gapExtra pointExtended =>
                              exact Exists.intro gap
                                (Exists.intro extendedGap
                                  (And.intro gapUnary
                                    (And.intro
                                      (unary_cont_closed gapUnary extraUnary gapExtra)
                                      (And.intro pointGap
                                        (And.intro gapExtra pointExtended)))))

theorem HolomorphicOpenDisk_radius_continuation_extend
    {center point radius extra radius' : BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> UnaryHistory extra ->
      Cont radius extra radius' -> HolomorphicOpenDiskWitnessed center radius' point := by
  intro disk extraUnary radiusExtension
  have extension :=
    HolomorphicOpenDisk_radius_extension_gap_witness disk extraUnary radiusExtension
  cases disk with
  | intro centerUnary diskRest =>
      cases diskRest with
      | intro radiusUnary diskRest =>
          cases diskRest with
          | intro pointUnary _gapWitness =>
              cases extension with
              | intro _gap extensionRest =>
                  cases extensionRest with
                  | intro extendedGap extensionData =>
                      cases extensionData with
                      | intro _gapUnary extensionData =>
                          cases extensionData with
                          | intro extendedGapUnary extensionData =>
                              cases extensionData with
                              | intro _pointGap extensionData =>
                                  cases extensionData with
                                  | intro _gapExtra pointExtended =>
                                      exact And.intro centerUnary
                                        (And.intro
                                          (unary_cont_closed radiusUnary extraUnary radiusExtension)
                                          (And.intro pointUnary
                                            (Exists.intro extendedGap
                                              (And.intro extendedGapUnary pointExtended))))

end BEDC.Derived.HolomorphicUp
