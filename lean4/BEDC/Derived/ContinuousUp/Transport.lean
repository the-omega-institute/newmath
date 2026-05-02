import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_hsame_transport
    {source map target modulus cert source' map' target' modulus' cert' : BHist} :
    hsame source source' →
      hsame map map' →
        hsame target target' →
          hsame modulus modulus' →
            hsame cert cert' →
              ContinuousFunctionCarrier source map target modulus cert →
                ContinuousFunctionCarrier source' map' target' modulus' cert' := by
  intro sameSource sameMap sameTarget sameModulus sameCert carrier
  cases carrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro targetCarrier rest =>
          cases rest with
          | intro mapCarrier rest =>
              cases rest with
              | intro modulusCarrier rest =>
                  cases rest with
                  | intro sourceMap targetCert =>
                      cases sameSource
                      cases sameMap
                      cases sameTarget
                      cases sameModulus
                      cases sameCert
                      exact
                        And.intro sourceCarrier
                          (And.intro targetCarrier
                            (And.intro mapCarrier
                              (And.intro modulusCarrier (And.intro sourceMap targetCert))))

end BEDC.Derived.ContinuousUp
