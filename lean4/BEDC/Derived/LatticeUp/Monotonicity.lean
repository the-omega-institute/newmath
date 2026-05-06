import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.Derived.PreorderUp

theorem LatticeSingletonMeet_monotone_empty {a a' b b' : BHist} :
    LatticeSingletonCarrier a ->
      LatticeSingletonCarrier a' ->
        LatticeSingletonCarrier b ->
          LatticeSingletonCarrier b' ->
            LatticeSingletonLE a a' ->
              LatticeSingletonLE b b' ->
                LatticeSingletonLE (LatticeSingletonMeet a b) (LatticeSingletonMeet a' b') ∧
                  hsame (LatticeSingletonMeet a b) BHist.Empty ∧
                    hsame (LatticeSingletonMeet a' b') BHist.Empty := by
  intro _carrierA _carrierA' _carrierB _carrierB' _leAA' _leBB'
  have meetEmpty : hsame (LatticeSingletonMeet a b) BHist.Empty := hsame_refl BHist.Empty
  have meetEmpty' : hsame (LatticeSingletonMeet a' b') BHist.Empty :=
    hsame_refl BHist.Empty
  have meetLE :
      LatticeSingletonLE (LatticeSingletonMeet a b) (LatticeSingletonMeet a' b') :=
    ⟨meetEmpty, meetEmpty',
      PreorderPrefixLE_of_hsame (hsame_trans meetEmpty (hsame_symm meetEmpty'))⟩
  exact ⟨meetLE, meetEmpty, meetEmpty'⟩

end BEDC.Derived.LatticeUp
