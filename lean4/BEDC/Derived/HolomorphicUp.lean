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

def HolomorphicOpenDiskGap (z0 r z gap : BHist) : Prop :=
  UnaryHistory z0 ∧ UnaryHistory r ∧ UnaryHistory z ∧ UnaryHistory gap ∧ Cont z gap r

theorem HolomorphicOpenDiskGap_transport_certificate {z0 z0' r r' z z' gap gap' : BHist} :
    HolomorphicOpenDiskGap z0 r z gap -> hsame z0 z0' -> hsame r r' -> hsame z z' ->
      hsame gap gap' -> HolomorphicOpenDiskGap z0' r' z' gap' ∧ UnaryHistory gap' ∧
        Cont z' gap' r' := by
  intro disk sameZ0 sameR sameZ sameGap
  cases disk with
  | intro z0Carrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have z0Carrier' : UnaryHistory z0' := unary_transport z0Carrier sameZ0
                  have radiusCarrier' : UnaryHistory r' := unary_transport radiusCarrier sameR
                  have pointCarrier' : UnaryHistory z' := unary_transport pointCarrier sameZ
                  have gapCarrier' : UnaryHistory gap' := unary_transport gapCarrier sameGap
                  have pointGap' : Cont z' gap' r' :=
                    cont_hsame_transport sameZ sameGap sameR pointGap
                  exact
                    And.intro
                      (And.intro z0Carrier'
                        (And.intro radiusCarrier'
                          (And.intro pointCarrier'
                            (And.intro gapCarrier' pointGap'))))
                      (And.intro gapCarrier' pointGap')

theorem HolomorphicOpenDiskGap_unary_suffix_transport {z0 r z gap q zq rq : BHist} :
    HolomorphicOpenDiskGap z0 r z gap -> UnaryHistory q -> Cont z q zq -> Cont r q rq ->
      HolomorphicOpenDiskGap z0 rq zq gap ∧ Cont zq gap rq := by
  intro disk suffixCarrier pointSuffix radiusSuffix
  cases disk with
  | intro z0Carrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have shiftedPointCarrier : UnaryHistory zq :=
                    unary_cont_closed pointCarrier suffixCarrier pointSuffix
                  have shiftedRadiusCarrier : UnaryHistory rq :=
                    unary_cont_closed radiusCarrier suffixCarrier radiusSuffix
                  have shiftedBoundary : Cont zq gap rq := by
                    apply cont_intro
                    exact
                      radiusSuffix.trans
                        ((congrArg (fun h => append h q) pointGap).trans
                          ((append_assoc z gap q).trans
                            ((congrArg (append z)
                              (unary_append_comm gapCarrier suffixCarrier)).trans
                              ((append_assoc z q gap).symm.trans
                                (congrArg (fun h => append h gap) pointSuffix.symm)))))
                  exact
                    And.intro
                      (And.intro z0Carrier
                        (And.intro shiftedRadiusCarrier
                          (And.intro shiftedPointCarrier
                            (And.intro gapCarrier shiftedBoundary))))
                      shiftedBoundary

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
