import BEDC.Derived.ContinuousUp.Transport
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ContinuousFunctionCarrier_certificate_semanticNameCert
    {source map target modulus cert : BHist}
    (carrier : ContinuousFunctionCarrier source map target modulus cert) :
    SemanticNameCert (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
      (fun c : BHist => ContinuousFunctionCarrier source map target modulus c)
      (fun c : BHist => ContinuousFunctionCarrier source map target modulus c) hsame := by
  constructor
  · constructor
    · exact Exists.intro cert carrier
    · intro c _displayed
      exact hsame_refl c
    · intro c c' same
      exact hsame_symm same
    · intro c c' c'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro c c' same displayed
      exact
        ContinuousFunctionCarrier_hsame_transport (hsame_refl source) (hsame_refl map)
          (hsame_refl target) (hsame_refl modulus) same displayed
  · intro _c displayed
    exact displayed
  · intro _c displayed
    exact displayed

end BEDC.Derived.ContinuousUp
