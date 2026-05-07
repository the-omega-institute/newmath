import BEDC.FKernel.Cont
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

end BEDC.Derived.QuantumChannelUp
