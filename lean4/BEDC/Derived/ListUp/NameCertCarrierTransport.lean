import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem ListClassifierSpec_nameCert_carrier_transport
    {Carrier : BHist -> Prop} {sameA : BHist -> BHist -> Prop}
    (cert : BEDC.FKernel.NameCert.NameCert Carrier sameA) :
    forall {xs ys : ListCarrier BHist},
      ListClassifierSpec (fun h k => Carrier h /\ sameA h k) xs ys ->
        ListClassifierSpec (fun _ k => Carrier k) ys ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases classified
  | cons x xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons y ys =>
          cases classified with
          | intro head tail =>
              constructor
              · exact cert.carrier_respects_equiv head.right head.left
              · exact ih tail

end BEDC.Derived.ListUp
