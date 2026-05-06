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

end BEDC.Derived.QuantumChannelUp
