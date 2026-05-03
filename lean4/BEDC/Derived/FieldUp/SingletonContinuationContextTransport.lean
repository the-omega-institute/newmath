import BEDC.Derived.FieldUp.SingletonClassifierEndpointTransport

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_two_sided_context_transport_iff
    {L R h mid out S : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> Cont L h mid -> Cont mid R out ->
      (FieldSingletonClassifier out S <-> FieldSingletonClassifier h S) := by
  intro carrierL carrierR leftContinuation rightContinuation
  have outMid :
      FieldSingletonClassifier out S <-> FieldSingletonClassifier mid S :=
    FieldSingletonClassifier_continuation_left_endpoint_transport_iff carrierR rightContinuation
  have midH :
      FieldSingletonClassifier mid S <-> FieldSingletonClassifier h S :=
    FieldSingletonClassifier_continuation_right_endpoint_transport_iff carrierL leftContinuation
  constructor
  · intro classified
    exact Iff.mp midH (Iff.mp outMid classified)
  · intro classified
    exact Iff.mpr outMid (Iff.mpr midH classified)

end BEDC.Derived.FieldUp
