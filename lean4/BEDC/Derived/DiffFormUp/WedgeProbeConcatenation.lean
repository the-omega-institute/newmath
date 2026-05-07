import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem DiffFormWedgeProbeConcatenation_classifier_stability
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' e q u r b m e' q' u' r' b' m' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes e q u r b m e' q' u' r' b' m' ->
        hsame (append l m) (append l' m') := by
  intro leftRows rightRows
  cases leftRows.right.right.right.right.right.right.right
  cases rightRows.right.right.right.right.right.right.right
  rfl

end BEDC.Derived.DiffFormUp
