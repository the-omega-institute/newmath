import BEDC.FKernel.Sig.SameSig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sameSig_endpoint_replacement [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} (policy : AskPolicy D) {h h' k k' : BHist} :
    D h -> D h' -> D k -> D k' -> hsame h h' -> SameSig bundle h k ->
      hsame k k' -> SameSig bundle h' k' := by
  intro dh dh' dk dk' sameHH' sameHK sameKK'
  have sameHH'Sig : SameSig bundle h h' :=
    sameSig_of_hsame_from_ask_policy
      (bundle := bundle) (D := D) policy dh dh' sameHH'
  have sameH'H : SameSig bundle h' h := sameSig_symm sameHH'Sig
  have sameH'K : SameSig bundle h' k :=
    sameSig_trans
      (bundle := bundle) (D := D) (h := h') (k := h) (l := k)
      policy dh sameH'H sameHK
  have sameKK'Sig : SameSig bundle k k' :=
    sameSig_of_hsame_from_ask_policy
      (bundle := bundle) (D := D) policy dk dk' sameKK'
  exact
    sameSig_trans
      (bundle := bundle) (D := D) (h := h') (k := k) (l := k')
      policy dk sameH'K sameKK'Sig

end BEDC.FKernel.Sig
