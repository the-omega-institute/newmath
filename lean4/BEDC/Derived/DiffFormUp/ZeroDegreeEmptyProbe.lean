import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DiffFormZeroDegree_empty_probe_exhaustion {probe : BHist} :
    InBundle probe (ProbeBundle.Bnil : ProbeBundle BHist) -> False := by
  intro probeIn
  exact inBundle_nil_elim probeIn

theorem DiffFormZeroDegree_scalar_classifier_readback
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (_scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {scalar scalar' ledger ledger' : BHist} :
    ScalarClassifier scalar scalar' -> hsame ledger ledger' ->
      DiffFormBHistClassifier ScalarClassifier ProbeBundle.Bnil BHist.Empty BHist.Empty
        BHist.Empty scalar BHist.Empty ledger BHist.Empty BHist.Empty BHist.Empty scalar'
        BHist.Empty ledger' ->
        ScalarClassifier scalar scalar' ∧ hsame ledger ledger' ∧
          (forall probe : BHist, InBundle probe (ProbeBundle.Bnil : ProbeBundle BHist) ->
            False) := by
  intro _scalarRows _ledgerRows classifierRows
  exact And.intro classifierRows.right.right.right.right.right.left
    (And.intro classifierRows.right.right.right.right.right.right.right
      (fun probe probeIn => DiffFormZeroDegree_empty_probe_exhaustion (probe := probe) probeIn))

end BEDC.Derived.DiffFormUp
