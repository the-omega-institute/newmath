import BEDC.Derived.ComplexDiffUp
import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.DerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.MetricUp

def DerivativeMetricQuotient (f z h q dist : BHist) : Prop :=
  UnaryHistory f ∧ UnaryHistory z ∧ CplxNonZero h ∧ UnaryHistory q ∧ Cont f h q ∧
    UnaryHistory h ∧ UnaryHistory dist ∧ Cont h q dist

theorem DerivativeMetricQuotient_hsame_transport
    {f f' z z' h h' q q' dist dist' : BHist} :
    hsame f f' -> hsame z z' -> hsame h h' -> hsame q q' -> hsame dist dist' ->
      DerivativeMetricQuotient f z h q dist ->
        DerivativeMetricQuotient f' z' h' q' dist' ∧
          CplxDiffQuot f' z' h' q' ∧ MetricDistanceWitness h' q' dist' ∧
            Cont f' h' q' ∧ Cont h' q' dist' := by
  intro sameF sameZ sameH sameQ sameDist quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier rest =>
                  cases rest with
                  | intro diffLedger rest =>
                      cases rest with
                      | intro stepCarrier rest =>
                          cases rest with
                          | intro distCarrier metricLedger =>
                              have functionCarrier' : UnaryHistory f' :=
                                unary_transport functionCarrier sameF
                              have pointCarrier' : UnaryHistory z' :=
                                unary_transport pointCarrier sameZ
                              have stepCarrier' : UnaryHistory h' :=
                                unary_transport stepCarrier sameH
                              have quotientCarrier' : UnaryHistory q' :=
                                unary_transport quotientCarrier sameQ
                              have distCarrier' : UnaryHistory dist' :=
                                unary_transport distCarrier sameDist
                              have stepNonzero' : CplxNonZero h' := by
                                intro stepEmpty
                                exact stepNonzero (hsame_trans sameH stepEmpty)
                              have diffLedger' : Cont f' h' q' :=
                                cont_hsame_transport sameF sameH sameQ diffLedger
                              have metricWitness : MetricDistanceWitness h q dist :=
                                And.intro stepCarrier
                                  (And.intro quotientCarrier
                                    (And.intro distCarrier metricLedger))
                              have metricLedger' : Cont h' q' dist' :=
                                MetricDistanceWitness_cont_hsame_transport sameH sameQ sameDist
                                  metricWitness
                              have derivative' : DerivativeMetricQuotient f' z' h' q' dist' :=
                                And.intro functionCarrier'
                                  (And.intro pointCarrier'
                                    (And.intro stepNonzero'
                                      (And.intro quotientCarrier'
                                        (And.intro diffLedger'
                                          (And.intro stepCarrier'
                                            (And.intro distCarrier' metricLedger'))))))
                              have complexQuotient' : CplxDiffQuot f' z' h' q' :=
                                And.intro functionCarrier'
                                  (And.intro pointCarrier'
                                    (And.intro stepNonzero'
                                      (And.intro quotientCarrier' diffLedger')))
                              have metricWitness' : MetricDistanceWitness h' q' dist' :=
                                And.intro stepCarrier'
                                  (And.intro quotientCarrier'
                                    (And.intro distCarrier' metricLedger'))
                              exact And.intro derivative'
                                (And.intro complexQuotient'
                                  (And.intro metricWitness'
                                    (And.intro diffLedger' metricLedger')))

end BEDC.Derived.DerivativeUp
