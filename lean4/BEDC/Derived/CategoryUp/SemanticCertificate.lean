import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist

theorem CategoryHomCarrier_semanticNameCert_of_hom {a b f : BHist} :
    CategoryHomCarrier a b f ->
      BEDC.FKernel.NameCert.SemanticNameCert (CategoryHomCarrier a b)
        (CategoryHomCarrier a b) (CategoryHomCarrier a b) hsame := by
  intro homCarrier
  constructor
  · constructor
    · exact Exists.intro f homCarrier
    · intro h _homCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      exact CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrierH
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.CategoryUp
