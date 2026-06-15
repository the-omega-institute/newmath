import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CriticalLineWitnessCarrier_phase_real_classifier_determinacy
    {Z S M R Q H C P N Z' S' M' R' Q' H' C' P' N' phaseRead phaseRead' : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      CriticalLineWitnessCarrier Z' S' M' R' Q' H' C' P' N' ->
        hsame Z Z' ->
          hsame S S' ->
            hsame M M' ->
              hsame R R' ->
                hsame Q Q' ->
                  hsame H H' ->
                    hsame C C' ->
                      hsame P P' ->
                        hsame N N' ->
                          Cont Z S phaseRead ->
                            Cont Z' S' phaseRead' -> hsame phaseRead phaseRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro _packet _packet' sameZ sameS _sameM _sameR _sameQ _sameH _sameC _sameP _sameN
    phaseRoute phaseRoute'
  exact cont_respects_hsame sameZ sameS phaseRoute phaseRoute'

end BEDC.Derived.CriticalLineWitnessUp
