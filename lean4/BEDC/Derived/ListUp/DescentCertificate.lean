import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_descentCertificate_map {A B : Type}
    {sourceSame : A -> A -> Prop} {targetSame : B -> B -> Prop}
    (cert : BEDC.FKernel.NameCert.DescentCertificate A B sourceSame targetSame) :
    forall {xs ys : ListCarrier A},
      ListClassifierSpec sourceSame xs ys ->
        ListClassifierSpec targetSame (xs.map cert.map) (ys.map cert.map) := by
  intro xs
  induction xs with
  | nil =>
      intro ys same
      cases ys with
      | nil =>
          constructor
      | cons _ _ =>
          cases same
  | cons x xs ih =>
      intro ys same
      cases ys with
      | nil =>
          cases same
      | cons y ys =>
          cases same with
          | intro headSame tailSame =>
              constructor
              · exact BEDC.FKernel.NameCert.descentCertificate_respects cert headSame
              · exact ih tailSame

end BEDC.Derived.ListUp
