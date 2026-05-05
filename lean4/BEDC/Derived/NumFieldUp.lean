import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding
import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

def NumFieldRatReflexiveCarrier (h : BHist) : Prop :=
  RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h) ∧
    Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h)

theorem NumFieldRatReflexive_finite_basis_witness {h : BHist} :
    NumFieldRatReflexiveCarrier h ->
      RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
        Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) ∧
          RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
            (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) := by
  intro carrier
  have basisCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have basisContinuation : Cont h (BHist.e1 BHist.Empty) (append h (BHist.e1 BHist.Empty)) :=
    cont_intro rfl
  have sourceClassified : RatHistoryClassifier h (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.right
  have appendedClassified :
      RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified
      (unary_e1_closed unary_empty) (hsame_refl (BHist.e1 BHist.Empty))
  exact And.intro basisCarrier (And.intro basisContinuation appendedClassified)

end BEDC.Derived.NumFieldUp
