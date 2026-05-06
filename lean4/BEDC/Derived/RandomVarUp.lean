import BEDC.FKernel.Hist
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

theorem RandomVarPreimage_disjoint_binary_union_exactness
    {B C U_T A_B A_C A_U U_S : BHist} :
    hsame A_B B -> hsame A_C C -> hsame A_U U_T -> Cont B C U_T ->
      Cont A_B A_C U_S -> (hsame B C -> False) ->
        hsame A_U U_S ∧ (hsame A_B A_C -> False) := by
  intro samePreimageB samePreimageC samePreimageUnion targetUnion sourceUnion targetDisjoint
  have transportedUnion : hsame U_T U_S :=
    cont_respects_hsame (hsame_symm samePreimageB) (hsame_symm samePreimageC)
      targetUnion sourceUnion
  have sourceDisjoint : hsame A_B A_C -> False := by
    intro sameSource
    exact targetDisjoint
      (hsame_trans (hsame_symm samePreimageB) (hsame_trans sameSource samePreimageC))
  exact And.intro (hsame_trans samePreimageUnion transportedUnion) sourceDisjoint

end BEDC.Derived.RandomVarUp
