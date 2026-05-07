import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Assoc
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary

namespace BEDC.Derived.QuantumChannelUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive QuantumChannelAffineMixtureSpine (channel : BHist -> Prop) : BHist -> Prop where
  | atom {phi : BHist} :
      channel phi -> UnaryHistory phi -> QuantumChannelAffineMixtureSpine channel phi
  | mix {phi psi out : BHist} :
      QuantumChannelAffineMixtureSpine channel phi ->
        QuantumChannelAffineMixtureSpine channel psi ->
          Cont phi psi out -> QuantumChannelAffineMixtureSpine channel out

theorem QuantumChannelAffineMixtureSpine_finite_closure
    {channel : BHist -> Prop} {phi : BHist}
    (binaryClosed :
      forall {left right out : BHist},
        channel left -> channel right -> Cont left right out -> channel out) :
    QuantumChannelAffineMixtureSpine channel phi -> channel phi := by
  intro spine
  induction spine with
  | atom channelPhi _ =>
      exact channelPhi
  | mix leftSpine rightSpine route leftChannel rightChannel =>
      exact binaryClosed leftChannel rightChannel route

theorem QuantumChannelAffineMixtureSpine_density_preservation
    {channel density : BHist -> Prop} {phi : BHist}
    (atomDensity : forall {h : BHist}, channel h -> UnaryHistory h -> density h)
    (densityBinaryClosed :
      forall {left right out : BHist},
        density left -> density right -> Cont left right out -> density out) :
    QuantumChannelAffineMixtureSpine channel phi -> density phi := by
  intro spine
  induction spine with
  | atom channelPhi unaryPhi =>
      exact atomDensity channelPhi unaryPhi
  | mix leftSpine rightSpine route leftDensity rightDensity =>
      exact densityBinaryClosed leftDensity rightDensity route

theorem QuantumChannelSingleton_identity_channel_cptp {rho image : BHist} :
    UnaryHistory rho -> hsame rho BHist.Empty -> Cont BHist.Empty rho image ->
      QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) image ∧
        hsame image rho ∧ hsame image BHist.Empty := by
  intro unaryRho rhoEmpty identityCont
  have imageRho : hsame image rho := cont_left_unit_result identityCont
  have imageEmpty : hsame image BHist.Empty := hsame_trans imageRho rhoEmpty
  have unaryImage : UnaryHistory image := unary_transport unaryRho (hsame_symm imageRho)
  exact And.intro
    (QuantumChannelAffineMixtureSpine.atom imageEmpty unaryImage)
    (And.intro imageRho imageEmpty)

theorem QuantumChannelAffineMixtureSpine_composition_assoc
    {channel : BHist -> Prop} {phi psi theta phiPsi psiTheta left right : BHist}
    (binaryClosed :
      forall {a b out : BHist}, channel a -> channel b -> Cont a b out -> channel out) :
    QuantumChannelAffineMixtureSpine channel phi ->
      QuantumChannelAffineMixtureSpine channel psi ->
        QuantumChannelAffineMixtureSpine channel theta ->
          Cont phi psi phiPsi ->
            Cont psi theta psiTheta ->
              Cont phiPsi theta left ->
                Cont phi psiTheta right -> channel left ∧ channel right ∧ hsame left right := by
  intro phiSpine psiSpine thetaSpine phiPsiCont psiThetaCont leftCont rightCont
  have phiChannel : channel phi :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed phiSpine
  have psiChannel : channel psi :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed psiSpine
  have thetaChannel : channel theta :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed thetaSpine
  have phiPsiChannel : channel phiPsi := binaryClosed phiChannel psiChannel phiPsiCont
  have psiThetaChannel : channel psiTheta := binaryClosed psiChannel thetaChannel psiThetaCont
  exact And.intro
    (binaryClosed phiPsiChannel thetaChannel leftCont)
    (And.intro
      (binaryClosed phiChannel psiThetaChannel rightCont)
      (cont_assoc_up_to_hsame_spine phiPsiCont leftCont psiThetaCont rightCont))

theorem QuantumChannelAffineMixtureSpine_composition_closure
    {channel : BHist -> Prop} {phi psi out : BHist}
    (binaryClosed :
      forall {left right result : BHist},
        channel left -> channel right -> Cont left right result -> channel result) :
    QuantumChannelAffineMixtureSpine channel phi ->
      QuantumChannelAffineMixtureSpine channel psi ->
        Cont phi psi out -> channel out ∧ QuantumChannelAffineMixtureSpine channel out := by
  intro phiSpine psiSpine composition
  have phiChannel : channel phi :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed phiSpine
  have psiChannel : channel psi :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed psiSpine
  exact And.intro
    (binaryClosed phiChannel psiChannel composition)
    (QuantumChannelAffineMixtureSpine.mix phiSpine psiSpine composition)

theorem QuantumChannelAffineMixtureSpine_unit_laws
    {channel : BHist -> Prop} {phi left right : BHist}
    (binaryClosed :
      forall {a b out : BHist}, channel a -> channel b -> Cont a b out -> channel out)
    (emptyChannel : channel BHist.Empty) :
    QuantumChannelAffineMixtureSpine channel phi ->
      Cont BHist.Empty phi left ->
        Cont phi BHist.Empty right ->
          channel left ∧ channel right ∧ hsame left phi ∧ hsame right phi := by
  intro phiSpine leftCont rightCont
  have phiChannel : channel phi :=
    QuantumChannelAffineMixtureSpine_finite_closure binaryClosed phiSpine
  exact And.intro
    (binaryClosed emptyChannel phiChannel leftCont)
    (And.intro
      (binaryClosed phiChannel emptyChannel rightCont)
      (And.intro (cont_left_unit_result leftCont) (cont_right_unit_result rightCont)))

theorem QuantumChannelAffineMixtureSpine_density_mixture_preservation {phi rho image : BHist} :
    QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) phi ->
      hsame rho BHist.Empty -> Cont phi rho image ->
        hsame image BHist.Empty ∧
          QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) image := by
  intro spine rhoEmpty densityCont
  have phiEmpty : hsame phi BHist.Empty :=
    QuantumChannelAffineMixtureSpine_finite_closure
      (channel := fun h : BHist => hsame h BHist.Empty)
      (fun {left right out} leftEmpty rightEmpty mixtureCont => by
        cases leftEmpty
        exact cont_left_unit_result mixtureCont |>.trans rightEmpty)
      spine
  have imageRho : hsame image rho := cont_left_unit_result (by
    cases phiEmpty
    exact densityCont)
  have imageEmpty : hsame image BHist.Empty := hsame_trans imageRho rhoEmpty
  have imageUnary : UnaryHistory image := unary_transport unary_empty (hsame_symm imageEmpty)
  exact And.intro imageEmpty (QuantumChannelAffineMixtureSpine.atom imageEmpty imageUnary)

theorem QuantumChannelSingleton_identity_composition_unit_laws {phi left right : BHist} :
    QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) phi ->
      Cont BHist.Empty phi left -> Cont phi BHist.Empty right ->
        hsame left phi ∧ hsame right phi ∧
          QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) left ∧
            QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) right := by
  intro spine leftCont rightCont
  have phiEmpty : hsame phi BHist.Empty :=
    QuantumChannelAffineMixtureSpine_finite_closure
      (channel := fun h : BHist => hsame h BHist.Empty)
      (fun {left right out} leftEmpty rightEmpty mixtureCont => by
        cases leftEmpty
        exact hsame_trans (cont_left_unit_result mixtureCont) rightEmpty)
      spine
  have leftPhi : hsame left phi := cont_left_unit_result leftCont
  have rightPhi : hsame right phi :=
    Iff.mp cont_right_unit_iff rightCont
  have leftEmpty : hsame left BHist.Empty := hsame_trans leftPhi phiEmpty
  have rightEmpty : hsame right BHist.Empty := hsame_trans rightPhi phiEmpty
  have leftUnary : UnaryHistory left := unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right := unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro leftPhi
    (And.intro rightPhi
      (And.intro
        (QuantumChannelAffineMixtureSpine.atom leftEmpty leftUnary)
        (QuantumChannelAffineMixtureSpine.atom rightEmpty rightUnary)))

theorem QuantumChannelUnitaryConjugation_composition_law {U V T vT left right : BHist} :
    hsame U BHist.Empty -> hsame V BHist.Empty -> hsame T BHist.Empty ->
      Cont V T vT -> Cont U vT left -> Cont (append U V) T right ->
        hsame left right ∧
          QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) left ∧
            QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) right := by
  intro uEmpty vEmpty tEmpty vTCont leftCont rightCont
  have vTEmpty : hsame vT BHist.Empty := by
    cases vEmpty
    exact hsame_trans (cont_left_unit_result vTCont) tEmpty
  have leftEmpty : hsame left BHist.Empty := by
    cases uEmpty
    exact hsame_trans (cont_left_unit_result leftCont) vTEmpty
  have appendUVEmpty : hsame (append U V) BHist.Empty := by
    exact Iff.mpr append_eq_empty_iff (And.intro uEmpty vEmpty)
  have rightEmpty : hsame right BHist.Empty := by
    exact
      cont_respects_hsame
        appendUVEmpty
        tEmpty
        rightCont
        (cont_right_unit BHist.Empty)
  have sameEndpoints : hsame left right := hsame_trans leftEmpty (hsame_symm rightEmpty)
  have leftUnary : UnaryHistory left := unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right := unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro sameEndpoints
    (And.intro
      (QuantumChannelAffineMixtureSpine.atom leftEmpty leftUnary)
      (QuantumChannelAffineMixtureSpine.atom rightEmpty rightUnary))

theorem QuantumChannelUnitaryConjugation_channel {U Uinv T right left : BHist} :
    hsame U BHist.Empty -> hsame Uinv BHist.Empty -> hsame T BHist.Empty ->
      Cont T Uinv right -> Cont U right left -> hsame left BHist.Empty ∧
        QuantumChannelAffineMixtureSpine (fun h : BHist => hsame h BHist.Empty) left := by
  intro uEmpty uinvEmpty tEmpty rightCont leftCont
  have rightEmpty : hsame right BHist.Empty := by
    cases tEmpty
    exact hsame_trans (cont_left_unit_result rightCont) uinvEmpty
  have leftEmpty : hsame left BHist.Empty := by
    cases uEmpty
    exact hsame_trans (cont_left_unit_result leftCont) rightEmpty
  have leftUnary : UnaryHistory left := unary_transport unary_empty (hsame_symm leftEmpty)
  exact And.intro leftEmpty (QuantumChannelAffineMixtureSpine.atom leftEmpty leftUnary)

end BEDC.Derived.QuantumChannelUp
