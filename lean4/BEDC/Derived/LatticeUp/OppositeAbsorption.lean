import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist

theorem LatticeOppositeAbsorptionFromDirectionalBounds {h k : BHist} :
    LatticeSingletonCarrier h →
      LatticeSingletonCarrier k →
        LatticeSingletonClassifier (LatticeSingletonMeet h (LatticeSingletonJoin k h)) h ∧
          LatticeSingletonClassifier (LatticeSingletonMeet (LatticeSingletonJoin h k) h) h ∧
            LatticeSingletonClassifier (LatticeSingletonJoin h (LatticeSingletonMeet k h)) h ∧
              LatticeSingletonClassifier (LatticeSingletonJoin (LatticeSingletonMeet h k) h) h ∧
                hsame (LatticeSingletonMeet h (LatticeSingletonJoin k h)) BHist.Empty ∧
                  hsame (LatticeSingletonJoin (LatticeSingletonMeet h k) h) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame
  intro carrierH _carrierK
  have emptyCarrier : LatticeSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyToH : hsame BHist.Empty h := hsame_symm carrierH
  have classified : LatticeSingletonClassifier BHist.Empty h :=
    ⟨emptyCarrier, carrierH, emptyToH⟩
  exact
    ⟨classified, classified, classified, classified, emptyCarrier, emptyCarrier⟩

end BEDC.Derived.LatticeUp
