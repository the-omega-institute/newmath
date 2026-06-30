import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Hist

theorem MetaCICNormalizationBudgetCarrier_candidate_route_scope
    {term term' candidate candidate' evidence evidence' normalization normalization'
      adequacy adequacy' replay replay' refusal refusal' transport transport'
      routes routes' provenance provenance' localName localName' : BHist} :
    MetaCICNormalizationBudgetUp.mk term candidate evidence normalization adequacy replay
        refusal transport routes provenance localName =
      MetaCICNormalizationBudgetUp.mk term' candidate' evidence' normalization'
        adequacy' replay' refusal' transport' routes' provenance' localName' →
      hsame (BHist.e0 candidate) (BHist.e0 candidate') ∧
        hsame (BHist.e0 evidence) (BHist.e0 evidence') ∧
          hsame (BHist.e0 normalization) (BHist.e0 normalization') ∧
            hsame (BHist.e0 adequacy) (BHist.e0 adequacy') ∧
              hsame (BHist.e0 provenance) (BHist.e0 provenance') := by
  -- BEDC touchpoint anchor: BHist hsame
  intro hpacket
  cases hpacket
  exact
    ⟨hsame_refl (BHist.e0 candidate), hsame_refl (BHist.e0 evidence),
      hsame_refl (BHist.e0 normalization), hsame_refl (BHist.e0 adequacy),
      hsame_refl (BHist.e0 provenance)⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
