import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Hist

theorem MetaCICNormalizationBudgetCarrier_obligation_surface
    {term term' candidate candidate' evidence evidence' normalization normalization'
      adequacy adequacy' replay replay' refusal refusal' transport transport'
      routes routes' provenance provenance' localName localName' : BHist} :
    MetaCICNormalizationBudgetUp.mk term candidate evidence normalization adequacy replay
        refusal transport routes provenance localName =
      MetaCICNormalizationBudgetUp.mk term' candidate' evidence' normalization'
        adequacy' replay' refusal' transport' routes' provenance' localName' →
      hsame (BHist.e0 term) (BHist.e0 term') ∧
        hsame (BHist.e0 candidate) (BHist.e0 candidate') ∧
          hsame (BHist.e0 evidence) (BHist.e0 evidence') ∧
            hsame (BHist.e0 normalization) (BHist.e0 normalization') ∧
              hsame (BHist.e0 adequacy) (BHist.e0 adequacy') ∧
                hsame (BHist.e0 replay) (BHist.e0 replay') ∧
                  hsame (BHist.e0 refusal) (BHist.e0 refusal') ∧
                    hsame (BHist.e0 transport) (BHist.e0 transport') ∧
                      hsame (BHist.e0 routes) (BHist.e0 routes') ∧
                        hsame (BHist.e0 provenance) (BHist.e0 provenance') ∧
                          hsame (BHist.e0 localName) (BHist.e0 localName') := by
  -- BEDC touchpoint anchor: BHist hsame
  intro hpacket
  cases hpacket
  exact
    ⟨hsame_refl (BHist.e0 term), hsame_refl (BHist.e0 candidate),
      hsame_refl (BHist.e0 evidence), hsame_refl (BHist.e0 normalization),
      hsame_refl (BHist.e0 adequacy), hsame_refl (BHist.e0 replay),
      hsame_refl (BHist.e0 refusal), hsame_refl (BHist.e0 transport),
      hsame_refl (BHist.e0 routes), hsame_refl (BHist.e0 provenance),
      hsame_refl (BHist.e0 localName)⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
