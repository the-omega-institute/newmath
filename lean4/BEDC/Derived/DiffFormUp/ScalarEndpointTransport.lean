import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DiffFormBHistCarrier_scalar_endpoint_transport {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' transportedScalar : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      ScalarClassifier s' transportedScalar ->
        DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t'
            transportedScalar a' l' ∧
          ScalarClassifier s transportedScalar := by
  intro rows scalarTransport
  have sourceScalar : ScalarClassifier s transportedScalar :=
    NameCert.equiv_trans scalarCert rows.right.right.right.right.right.left scalarTransport
  exact
    And.intro
      (And.intro rows.left
        (And.intro rows.right.left
          (And.intro rows.right.right.left
            (And.intro rows.right.right.right.left
              (And.intro rows.right.right.right.right.left
                (And.intro sourceScalar
                  (And.intro rows.right.right.right.right.right.right.left
                    rows.right.right.right.right.right.right.right)))))))
      sourceScalar

end BEDC.Derived.DiffFormUp
