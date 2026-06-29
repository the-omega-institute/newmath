import BEDC.Derived.PhenomenologyScienceInterfaceUp.TasteGate

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Hist

theorem PhenomenologyScienceInterface_gap_ledger (x : PhenomenologyScienceInterfaceUp) :
    ∃ R U O L S J B G H C P N : BHist,
      x = PhenomenologyScienceInterfaceUp.mk R U O L S J B G H C P N ∧
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N G ∧
          (∀ row : BHist,
            hsame row G →
              PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row) := by
  -- BEDC touchpoint anchor: BHist hsame
  cases x with
  | mk R U O L S J B G H C P N =>
      refine ⟨R, U, O, L, S, J, B, G, H, C, P, N, ?_⟩
      constructor
      · rfl
      · constructor
        · exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl (hsame_refl G))))))))
        · intro row sameRowG
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameRowG)))))))

end BEDC.Derived.PhenomenologyScienceInterfaceUp
