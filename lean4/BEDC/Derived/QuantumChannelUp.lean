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

end BEDC.Derived.QuantumChannelUp
