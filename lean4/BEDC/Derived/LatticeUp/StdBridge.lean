import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.PreorderUp

theorem LatticeUp_StdBridge :
    LatticeSingletonCarrier BHist.Empty ∧
      LatticeSingletonClassifier BHist.Empty BHist.Empty ∧
      LatticeSingletonLE BHist.Empty BHist.Empty ∧
      LatticeSingletonCarrier (LatticeSingletonMeet BHist.Empty BHist.Empty) ∧
      LatticeSingletonCarrier (LatticeSingletonJoin BHist.Empty BHist.Empty) ∧
      SemanticNameCert LatticeSingletonCarrier LatticeSingletonCarrier LatticeSingletonCarrier
        LatticeSingletonClassifier := by
  have laws := LatticeSingletonPrefix_laws
  have emptyCarrier : LatticeSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : LatticeSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have emptyOrder : LatticeSingletonLE BHist.Empty BHist.Empty :=
    And.intro emptyCarrier
      (And.intro emptyCarrier (PreorderPrefixLE_of_hsame (hsame_refl BHist.Empty)))
  exact
    And.intro emptyCarrier
      (And.intro emptyClassifier
        (And.intro emptyOrder
          (And.intro emptyCarrier
            (And.intro emptyCarrier laws.left))))

end BEDC.Derived.LatticeUp
