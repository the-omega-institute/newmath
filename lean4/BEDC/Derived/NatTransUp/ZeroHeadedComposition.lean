import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem NatTransPrefixComponentCarrier_vert_comp_zero_headed_component_absurd
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta →
      NatTransPrefixComponentCarrier q r a theta → Cont eta theta composite →
        ((∃ w : BHist, p = BHist.e0 w) ∨ (∃ w : BHist, q = BHist.e0 w) ∨
          (∃ w : BHist, r = BHist.e0 w) ∨ (∃ w : BHist, a = BHist.e0 w) ∨
            (∃ w : BHist, eta = BHist.e0 w) ∨
              (∃ w : BHist, theta = BHist.e0 w) ∨
                (∃ w : BHist, composite = BHist.e0 w)) →
          False := by
  intro left right comp zeroComponent
  have compositeCarrier : NatTransPrefixComponentCarrier p r a composite :=
    NatTransPrefixComponentCarrier_vert_comp_closed left right comp
  cases zeroComponent with
  | inl sourcePrefixZero =>
      exact NatTransPrefixComponentCarrier_zero_headed_component_absurd left
        (Or.inl sourcePrefixZero)
  | inr rest =>
      cases rest with
      | inl middlePrefixZero =>
          exact NatTransPrefixComponentCarrier_zero_headed_component_absurd left
            (Or.inr (Or.inl middlePrefixZero))
      | inr rest =>
          cases rest with
          | inl targetPrefixZero =>
              exact NatTransPrefixComponentCarrier_zero_headed_component_absurd right
                (Or.inr (Or.inl targetPrefixZero))
          | inr rest =>
              cases rest with
              | inl objectZero =>
                  exact NatTransPrefixComponentCarrier_zero_headed_component_absurd left
                    (Or.inr (Or.inr (Or.inl objectZero)))
              | inr rest =>
                  cases rest with
                  | inl leftComponentZero =>
                      exact NatTransPrefixComponentCarrier_zero_headed_component_absurd left
                        (Or.inr (Or.inr (Or.inr leftComponentZero)))
                  | inr rest =>
                      cases rest with
                      | inl rightComponentZero =>
                          exact NatTransPrefixComponentCarrier_zero_headed_component_absurd right
                            (Or.inr (Or.inr (Or.inr rightComponentZero)))
                      | inr compositeComponentZero =>
                          exact NatTransPrefixComponentCarrier_zero_headed_component_absurd
                            compositeCarrier (Or.inr (Or.inr (Or.inr compositeComponentZero)))

end BEDC.Derived.NatTransUp
