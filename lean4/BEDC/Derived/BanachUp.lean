import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem BanachSingletonEmptyHistory_carrier_classifier {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      VecSpaceSingletonClassifier m n ∧ FieldSingletonClassifier m n ∧
        RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierM carrierN
  have sameMN : hsame m n := hsame_trans carrierM (hsame_symm carrierN)
  have vecRow : VecSpaceSingletonClassifier m n :=
    And.intro carrierM (And.intro carrierN sameMN)
  have fieldCarrierM : FieldSingletonCarrier m := carrierM
  have fieldCarrierN : FieldSingletonCarrier n := carrierN
  have fieldRow : FieldSingletonClassifier m n :=
    And.intro fieldCarrierM (And.intro fieldCarrierN sameMN)
  have positiveDenominator : PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    Iff.mpr PositiveUnaryDenominator_e1_iff_unary unary_empty
  have intCarrier : BEDC.Derived.IntUp.IntCarrier BMark.b0 BHist.Empty :=
    And.intro (Or.inl rfl) unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    Exists.intro BMark.b0
      (Exists.intro BHist.Empty
        (RatCarrier_of_int_positive_denominator intCarrier positiveDenominator))
  have ratRow : RatHistoryClassifier (BHist.e1 BHist.Empty)
      (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier
      (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realRow :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr RealConstantHistoryClassifier_e1_iff_rat ratRow
  exact And.intro vecRow (And.intro fieldRow realRow)

end BEDC.Derived.BanachUp
