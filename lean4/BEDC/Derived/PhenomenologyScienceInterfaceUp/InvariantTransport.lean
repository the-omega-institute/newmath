import BEDC.Derived.PhenomenologyScienceInterfaceUp.TasteGate

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhenomenologyScienceInterface_invariant_transport
    (R U O L S J B G H C P N : BHist) :
    SemanticNameCert
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        hsame ∧
      PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N S ∧
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N J ∧
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N L ∧
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N O := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact
    ⟨PhenomenologyScienceInterfaceNameCertObligations R U O L S J B G H C P N,
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr (Or.inl (hsame_refl S))))),
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inl (hsame_refl J)))))),
      Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl L)))),
      Or.inr (Or.inr (Or.inl (hsame_refl O)))⟩

end BEDC.Derived.PhenomenologyScienceInterfaceUp
