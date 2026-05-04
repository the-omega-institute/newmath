import BEDC.Derived.ContinuousUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusChain_endpoint_cycle_moduli_empty
    {source first second target : BHist} :
    ContinuousModulusChain source first second target -> hsame source target ->
      hsame first BHist.Empty ∧ hsame second BHist.Empty := by
  intro chain sameEndpoint
  cases chain with
  | intro _sourceCarrier rest =>
      cases rest with
      | intro _firstCarrier rest =>
          cases rest with
          | intro _secondCarrier rest =>
              cases rest with
              | intro _targetCarrier witness =>
                  cases witness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          exact cont_mutual_extension_tails_empty firstRel
                            (cont_result_hsame_transport secondRel (hsame_symm sameEndpoint))

theorem ContinuousModulusWitness_endpoint_cycle_modulus_empty
    {source modulus target : BHist} :
    ContinuousModulusWitness source modulus target -> hsame source target ->
      hsame modulus BHist.Empty := by
  intro witness sameEndpoint
  exact cont_right_unit_unique
    (cont_result_hsame_transport witness.right.right.right (hsame_symm sameEndpoint))

theorem ContinuousFunctionCarrier_endpoint_cert_cycle_tails_empty
    {source map target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert -> hsame source cert ->
      hsame map BHist.Empty ∧ hsame modulus BHist.Empty := by
  intro carrier sameEndpoint
  exact
    cont_mutual_extension_tails_empty carrier.right.right.right.right.left
      (cont_result_hsame_transport carrier.right.right.right.right.right
        (hsame_symm sameEndpoint))

theorem ContinuousModulusChain_empty_second_witness {source first second target : BHist} :
    ContinuousModulusChain source first second target -> hsame second BHist.Empty ->
      ContinuousModulusWitness source first target := by
  intro chain secondEmpty
  cases chain with
  | intro sourceCarrier rest =>
      cases rest with
      | intro firstCarrier rest =>
          cases rest with
          | intro _secondCarrier rest =>
              cases rest with
              | intro targetCarrier witness =>
                  cases witness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          have sameTargetMiddle : hsame target middle :=
                            cont_respects_hsame (hsame_refl middle) secondEmpty secondRel
                              (cont_right_unit middle)
                          exact
                            And.intro sourceCarrier
                              (And.intro firstCarrier
                                (And.intro targetCarrier
                                  (cont_result_hsame_transport firstRel
                                    (hsame_symm sameTargetMiddle))))

end BEDC.Derived.ContinuousUp
