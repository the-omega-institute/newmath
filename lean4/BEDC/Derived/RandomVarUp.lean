import BEDC.FKernel.Cont

namespace BEDC.Derived.RandomVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure RandomVarTotalReadbackCertificate
    (targetTotal sourceTotal chosenPreimage : BHist) : Prop where
  chosen_readback : Cont targetTotal BHist.Empty chosenPreimage
  carried_total_bridge : Cont targetTotal BHist.Empty sourceTotal

theorem RandomVarTotalReadbackCertificate_composition_total_event_preimage_exactness
    {omegaU omegaT omegaS preY preX preYX : BHist} :
    RandomVarTotalReadbackCertificate omegaU omegaT preY ->
      RandomVarTotalReadbackCertificate omegaT omegaS preX ->
        Cont preY BHist.Empty preYX ->
          hsame preYX omegaS ∧ hsame preYX preY ∧ hsame preY omegaT ∧ hsame preX omegaS := by
  intro upperCert lowerCert compositeReadback
  have compositeChosen : hsame preYX preY :=
    cont_deterministic compositeReadback (cont_right_unit preY)
  have upperChosenTarget : hsame preY omegaT :=
    cont_deterministic upperCert.chosen_readback upperCert.carried_total_bridge
  have lowerTargetSource : hsame omegaT omegaS :=
    cont_deterministic (cont_right_unit omegaT) lowerCert.carried_total_bridge
  have lowerChosenSource : hsame preX omegaS :=
    cont_deterministic lowerCert.chosen_readback lowerCert.carried_total_bridge
  exact And.intro (hsame_trans compositeChosen (hsame_trans upperChosenTarget lowerTargetSource))
    (And.intro compositeChosen (And.intro upperChosenTarget lowerChosenSource))

end BEDC.Derived.RandomVarUp
