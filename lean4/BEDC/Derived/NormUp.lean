import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NormUp

open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def NormSingletonNorm (_m : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem NormSingletonEmptyHistory_carrier_classifier {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryCarrier (NormSingletonNorm m) ∧
        VecSpaceSingletonClassifier m n ∧
          RealConstantHistoryClassifier (NormSingletonNorm m) (NormSingletonNorm n) ∧
            hsame (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierM carrierN
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have realCarrier : RealConstantHistoryCarrier (NormSingletonNorm m) := by
    exact RealConstantHistoryCarrier_e1_iff_rat.mpr ratCarrier
  have vectorClassifier : VecSpaceSingletonClassifier m n :=
    And.intro carrierM (And.intro carrierN (hsame_trans carrierM (hsame_symm carrierN)))
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (NormSingletonNorm m) (NormSingletonNorm n) := by
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro realCarrier
    (And.intro vectorClassifier
      (And.intro realClassifier (hsame_refl (BHist.e1 (BHist.e1 BHist.Empty)))))

theorem NormSingletonEmptyHistory_laws {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryCarrier (NormSingletonNorm m) ∧
        RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          VecSpaceSingletonClassifier (VecSpaceSingletonSmul m n) BHist.Empty ∧
            VecSpaceSingletonClassifier m BHist.Empty ∧
              VecSpaceSingletonClassifier n BHist.Empty := by
  intro carrierM carrierN
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have realCarrier : RealConstantHistoryCarrier (NormSingletonNorm m) := by
    exact RealConstantHistoryCarrier_e1_iff_rat.mpr ratCarrier
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) := by
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have smulEmpty :
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul m n) BHist.Empty :=
    And.intro emptyVecCarrier (And.intro emptyVecCarrier (hsame_refl BHist.Empty))
  have mEmpty : VecSpaceSingletonClassifier m BHist.Empty :=
    And.intro carrierM (And.intro emptyVecCarrier carrierM)
  have nEmpty : VecSpaceSingletonClassifier n BHist.Empty :=
    And.intro carrierN (And.intro emptyVecCarrier carrierN)
  exact And.intro realCarrier
    (And.intro realClassifier
      (And.intro smulEmpty
        (And.intro mEmpty nEmpty)))

theorem NormSingletonEmptyHistory_zero_exactness {m : BHist} :
    VecSpaceSingletonCarrier m ->
      (RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) <->
        VecSpaceSingletonClassifier m BHist.Empty) := by
  intro carrierM
  constructor
  · intro _zeroClassified
    exact And.intro carrierM
      (And.intro (hsame_refl BHist.Empty) carrierM)
  · intro vectorClassified
    exact (NormSingletonEmptyHistory_carrier_classifier carrierM vectorClassified.right.left).right.right.left

theorem NormSingletonEmptyHistory_semantic_name_certificate :
    SemanticNameCert
      (fun m : BHist =>
        VecSpaceSingletonCarrier m ∧ RealConstantHistoryCarrier (NormSingletonNorm m))
      VecSpaceSingletonCarrier
      (fun m : BHist =>
        RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)))
      VecSpaceSingletonClassifier ∧
      (forall {m : BHist}, VecSpaceSingletonCarrier m ->
        (RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) <->
          VecSpaceSingletonClassifier m BHist.Empty)) := by
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyRealCarrier :
      RealConstantHistoryCarrier (NormSingletonNorm BHist.Empty) :=
    (NormSingletonEmptyHistory_carrier_classifier emptyVecCarrier emptyVecCarrier).left
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro BHist.Empty (And.intro emptyVecCarrier emptyRealCarrier)
        equiv_refl := by
          intro m source
          exact And.intro source.left (And.intro source.left (hsame_refl m))
        equiv_symm := by
          intro m n classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro m n r classifiedMN classifiedNR
          exact And.intro classifiedMN.left
            (And.intro classifiedNR.right.left
              (hsame_trans classifiedMN.right.right classifiedNR.right.right))
        carrier_respects_equiv := by
          intro m n classified _source
          have realCarrierN :
              RealConstantHistoryCarrier (NormSingletonNorm n) :=
            (NormSingletonEmptyHistory_carrier_classifier classified.right.left
              classified.right.left).left
          exact And.intro classified.right.left realCarrierN
      }
      pattern_sound := by
        intro m source
        exact source.left
      ledger_sound := by
        intro m source
        exact (NormSingletonEmptyHistory_zero_exactness source.left).mpr
          (And.intro source.left (And.intro emptyVecCarrier source.left))
    }
  · intro m carrierM
    exact NormSingletonEmptyHistory_zero_exactness carrierM

theorem NormUp_StdBridge :
    SemanticNameCert
      (fun m : BHist =>
        VecSpaceSingletonCarrier m ∧ RealConstantHistoryCarrier (NormSingletonNorm m))
      VecSpaceSingletonCarrier
      (fun m : BHist =>
        RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)))
      VecSpaceSingletonClassifier ∧
      (∀ {m : BHist}, VecSpaceSingletonCarrier m →
        VecSpaceSingletonClassifier m BHist.Empty ∧
          RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty))) ∧
        (∀ {m : BHist}, VecSpaceSingletonCarrier m →
          (RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) ↔
            VecSpaceSingletonClassifier m BHist.Empty)) := by
  have certificateRows := NormSingletonEmptyHistory_semantic_name_certificate
  constructor
  · exact certificateRows.left
  · constructor
    · intro m carrierM
      have exactness := NormSingletonEmptyHistory_zero_exactness carrierM
      have vectorClassified : VecSpaceSingletonClassifier m BHist.Empty :=
        And.intro carrierM (And.intro (hsame_refl BHist.Empty) carrierM)
      exact And.intro vectorClassified (exactness.mpr vectorClassified)
    · intro m carrierM
      exact certificateRows.right carrierM

end BEDC.Derived.NormUp
