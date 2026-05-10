import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormWedgeLedger_coverage
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' leftDegree rightDegree outDegree leftLedger
      rightLedger tensorLedger : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
          tensorLedger ->
        Cont t t' tensorLedger ->
          UnaryHistory tensorLedger ∧ hsame tensorLedger (append t t') ∧
            DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
              tensorLedger ∧
              hsame leftLedger rightLedger := by
  intro _classifier wedgeLedger tensorCont
  exact
    ⟨wedgeLedger.right.right.right.right.left, tensorCont, wedgeLedger,
      wedgeLedger.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
