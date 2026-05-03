import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.HolomorphicUp
