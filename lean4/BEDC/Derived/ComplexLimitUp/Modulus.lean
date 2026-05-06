import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexModulus (z m : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ UnaryHistory m ∧ ComplexDistance z BHist.Empty m

theorem ComplexModulus_hsame_transport {z z' m m' : BHist} :
    hsame z z' -> hsame m m' -> ComplexModulus z m -> ComplexModulus z' m' := by
  intro sameZ sameM modulus
  cases modulus with
  | intro carrierZ rest =>
      cases rest with
      | intro unaryM distance =>
          have carrierZ' : ComplexHistoryCarrier z' :=
            ComplexHistoryLedgerPolicy_visible_carrier (And.intro carrierZ sameZ)
          have unaryM' : UnaryHistory m' :=
            unary_transport unaryM sameM
          have distance' : ComplexDistance z' BHist.Empty m' :=
            (ComplexDistance_hsame_transport_with_relation sameZ (hsame_refl BHist.Empty)
              sameM distance).left
          exact And.intro carrierZ' (And.intro unaryM' distance')

def CplxMod (z M : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ UnaryHistory M ∧
    (ComplexDistance z BHist.Empty M ∨ ComplexDistance BHist.Empty z M)

end BEDC.Derived.ComplexLimitUp
