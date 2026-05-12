import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.RegularityModulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def RegularityModulusDyadicWindowCarrier
    (precision modulus window transport route provenance name : BHist) : Prop :=
  hsame precision precision ∧ hsame modulus modulus ∧ hsame window window ∧
    hsame transport transport ∧ Cont precision modulus route ∧
      hsame provenance provenance ∧ hsame name name

theorem RegularityModulusDyadicWindowCarrier_window_monotonicity
    {k m w h c p n k' c' : BHist}
    (packet : RegularityModulusDyadicWindowCarrier k m w h c p n)
    (precisionTransport : hsame k k') (routeTransport : Cont k' m c') :
    RegularityModulusDyadicWindowCarrier k' m w h c' p n := by
  cases packet with
  | intro _samePrecision rest =>
      cases rest with
      | intro sameModulus rest =>
          cases rest with
          | intro sameWindow rest =>
              cases rest with
              | intro sameTransport rest =>
                  cases rest with
                  | intro _route rest =>
                      cases rest with
                      | intro sameProvenance sameName =>
                          constructor
                          · exact hsame_trans (hsame_symm precisionTransport) precisionTransport
                          · constructor
                            · exact sameModulus
                            · constructor
                              · exact sameWindow
                              · constructor
                                · exact sameTransport
                                · constructor
                                  · exact routeTransport
                                  · constructor
                                    · exact sameProvenance
                                    · exact sameName

end BEDC.Derived.RegularityModulusUp
