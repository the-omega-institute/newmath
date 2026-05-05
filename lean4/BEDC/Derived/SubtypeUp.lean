import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubtypeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubtypeRestrictedClassifier_nameCert {S P : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop} {s0 : BHist} (cert : NameCert S Classifier)
    (s0S : S s0) (s0P : P s0)
    (stableP : forall {h k : BHist}, S h -> P h -> Classifier h k -> P k) :
    NameCert (fun h : BHist => S h ∧ P h) Classifier := by
  exact {
    carrier_inhabited := Exists.intro s0 (And.intro s0S s0P)
    equiv_refl := by
      intro h carrier
      exact NameCert.equiv_refl cert carrier.left
    equiv_symm := by
      intro h k classified
      exact NameCert.equiv_symm cert classified
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact NameCert.equiv_trans cert classifiedHK classifiedKR
    carrier_respects_equiv := by
      intro h k classified carrier
      have parentCarrier : S k :=
        NameCert.carrier_respects_equiv cert classified carrier.left
      have subtypeCarrier : P k :=
        stableP carrier.left carrier.right classified
      exact And.intro parentCarrier subtypeCarrier
  }

theorem SubtypeRestrictedCarrier_classifier_closed {S P : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop} (cert : NameCert S Classifier)
    (stableP : forall {h k : BHist}, S h -> P h -> Classifier h k -> P k)
    {h k : BHist} :
    S h ∧ P h -> Classifier h k -> S k ∧ P k := by
  intro carrier classified
  have parentCarrier : S k :=
    NameCert.carrier_respects_equiv cert classified carrier.left
  have subtypeCarrier : P k :=
    stableP carrier.left carrier.right classified
  exact And.intro parentCarrier subtypeCarrier

end BEDC.Derived.SubtypeUp
