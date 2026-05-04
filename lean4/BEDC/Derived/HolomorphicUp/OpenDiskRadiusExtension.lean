import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem OpenDisk_radius_extension_closed {z0 r z extra r' : BHist} :
    OpenDisk z0 r z -> UnaryHistory extra -> Cont r extra r' -> OpenDisk z0 r' z := by
  intro disk extraUnary radiusStep
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  have pointUnary : UnaryHistory z := ComplexHistoryCarrier_unary pointCarrier
                  have radiusCarrier' : UnaryHistory r' :=
                    unary_cont_closed radiusCarrier extraUnary radiusStep
                  have extendedGapUnary : UnaryHistory (append gap extra) :=
                    unary_append_closed gapData.left extraUnary
                  have extendedLedger : Cont (append gap extra) z r' :=
                    cont_intro
                      (radiusStep.trans
                        ((congrArg (fun h => append h extra) gapData.right).trans
                          ((append_assoc gap z extra).trans
                            ((congrArg (append gap)
                              (unary_append_comm pointUnary extraUnary)).trans
                              (append_assoc gap extra z).symm))))
                  exact And.intro centerCarrier
                    (And.intro radiusCarrier'
                      (And.intro pointCarrier
                        (Exists.intro (append gap extra)
                          (And.intro extendedGapUnary extendedLedger))))

theorem OpenDisk_radius_extension_gap_public_readback {z0 r z extra r' : BHist} :
    OpenDisk z0 r z -> UnaryHistory extra -> Cont r extra r' ->
      OpenDisk z0 r' z ∧
        (forall {displayedGap : BHist}, UnaryHistory displayedGap ->
          Cont displayedGap z r' ->
            Exists (fun gap : BHist =>
              UnaryHistory gap ∧ Cont gap z r ∧ hsame (append gap extra) displayedGap)) := by
  intro disk extraUnary radiusStep
  have extended : OpenDisk z0 r' z :=
    OpenDisk_radius_extension_closed disk extraUnary radiusStep
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro pointCarrier gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  have pointUnary : UnaryHistory z := ComplexHistoryCarrier_unary pointCarrier
                  have extendedLedger : Cont (append gap extra) z r' :=
                    cont_intro
                      (radiusStep.trans
                        ((congrArg (fun h => append h extra) gapData.right).trans
                          ((append_assoc gap z extra).trans
                            ((congrArg (append gap)
                              (unary_append_comm pointUnary extraUnary)).trans
                              (append_assoc gap extra z).symm))))
                  exact And.intro extended
                    (fun {_displayedGap} _displayedUnary displayedLedger =>
                      Exists.intro gap
                        (And.intro gapData.left
                          (And.intro gapData.right
                            (cont_right_cancel extendedLedger displayedLedger))))

end BEDC.Derived.HolomorphicUp
