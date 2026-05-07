import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

def SchemeAffineCoverCarrier (chart : BHist) : Prop :=
  RingedSpaceSingletonSurface BHist.Empty BHist.Empty BHist.Empty BHist.Empty chart ∧
    CommRingSingletonClassifier chart BHist.Empty

def SchemeAffineCoverClassifier (left right : BHist) : Prop :=
  SchemeAffineCoverCarrier left ∧ SchemeAffineCoverCarrier right ∧
    RingedSpaceSingletonStalkClassifier left right

theorem SchemeAffineCover_semantic_name_certificate :
    SemanticNameCert SchemeAffineCoverCarrier SchemeAffineCoverCarrier SchemeAffineCoverCarrier
      SchemeAffineCoverClassifier := by
  have emptyLedger : SheafBHistPointGermLedger BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
    And.intro unary_empty (And.intro unary_empty (cont_intro rfl))
  have emptyCommCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCommClassifier : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCommCarrier (And.intro emptyCommCarrier (hsame_refl BHist.Empty))
  have emptySurface :
      RingedSpaceSingletonSurface BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
    And.intro
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      (And.intro emptyLedger emptyCommClassifier)
  have emptyCarrier : SchemeAffineCoverCarrier BHist.Empty :=
    And.intro emptySurface emptyCommClassifier
  have emptyStalkCarrier : RingedSpaceSingletonStalkCarrier BHist.Empty :=
    And.intro emptyLedger (And.intro emptyCommCarrier emptyCommClassifier)
  constructor
  · constructor
    · exact Exists.intro BHist.Empty emptyCarrier
    · intro chart carrier
      cases carrier.right.right.right
      exact And.intro carrier
        (And.intro carrier
          (And.intro emptyStalkCarrier
            (And.intro emptyStalkCarrier carrier.right)))
    · intro left right classified
      exact And.intro classified.right.left
        (And.intro classified.left
          (And.intro classified.right.right.right.left
            (And.intro classified.right.right.left
              (And.intro classified.right.right.right.right.right.left
                (And.intro classified.right.right.right.right.left
                  (hsame_symm classified.right.right.right.right.right.right))))))
    · intro left mid right classifiedLM classifiedMR
      exact And.intro classifiedLM.left
        (And.intro classifiedMR.right.left
          (And.intro classifiedLM.right.right.left
            (And.intro classifiedMR.right.right.right.left
              (And.intro classifiedLM.right.right.right.right.left
                (And.intro classifiedMR.right.right.right.right.right.left
                  (hsame_trans classifiedLM.right.right.right.right.right.right
                    classifiedMR.right.right.right.right.right.right))))))
    · intro left right classified _carrier
      exact classified.right.left
  · intro chart source
    exact source
  · intro chart source
    exact source

end BEDC.Derived.SchemeUp
