import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RingMapZeroFiber_semantic_name_certificate
    {CarrierS CarrierT : BHist -> Prop}
    {ClassifierS ClassifierT : BHist -> BHist -> Prop}
    {f : BHist -> BHist} {zeroT : BHist}
    (sourceCert : NameCert CarrierS ClassifierS)
    (targetCert : NameCert CarrierT ClassifierT)
    (mapClassifier :
      forall {x y : BHist}, CarrierS x -> CarrierS y -> ClassifierS x y ->
        ClassifierT (f x) (f y))
    (fiberWitness : exists x : BHist, RingMapZeroFiber CarrierS ClassifierT f zeroT x) :
    SemanticNameCert (RingMapZeroFiber CarrierS ClassifierT f zeroT)
      (RingMapZeroFiber CarrierS ClassifierT f zeroT)
      (RingMapZeroFiber CarrierS ClassifierT f zeroT) ClassifierS := by
  exact {
    core := {
      carrier_inhabited := fiberWitness
      equiv_refl := by
        intro h fiberH
        exact NameCert.equiv_refl sourceCert fiberH.left
      equiv_symm := by
        intro h k sameHK
        exact NameCert.equiv_symm sourceCert sameHK
      equiv_trans := by
        intro h k r sameHK sameKR
        exact NameCert.equiv_trans sourceCert sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK fiberH
        have carrierK : CarrierS k :=
          NameCert.carrier_respects_equiv sourceCert sameHK fiberH.left
        have imageHK : ClassifierT (f h) (f k) :=
          mapClassifier fiberH.left carrierK sameHK
        have imageKH : ClassifierT (f k) (f h) :=
          NameCert.equiv_symm targetCert imageHK
        exact And.intro carrierK (NameCert.equiv_trans targetCert imageKH fiberH.right)
    }
    pattern_sound := by
      intro _h fiberH
      exact fiberH
    ledger_sound := by
      intro _h fiberH
      exact fiberH
  }

end BEDC.Derived.IdealUp
