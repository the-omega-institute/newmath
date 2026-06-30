import BEDC.Derived.PhenomenologyScienceInterfaceUp.InvariantTransport

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhenomenologyScienceInterfaceObservationSlice
    (R U O L S J B G H C P N : BHist) :
    SemanticNameCert
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        (PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N)
        hsame ∧
      PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N R ∧
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N U ∧
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N O ∧
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N L := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact
    ⟨PhenomenologyScienceInterfaceNameCertObligations R U O L S J B G H C P N,
      Or.inl (hsame_refl R),
      Or.inr (Or.inl (hsame_refl U)),
      Or.inr (Or.inr (Or.inl (hsame_refl O))),
      Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl L))))⟩

end BEDC.Derived.PhenomenologyScienceInterfaceUp
