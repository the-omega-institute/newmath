import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparableExtUp

open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SeparableExtSimpleRoot_obligation
    {fieldPacket polynomialPacket minimalPolynomial derivativeWitness simpleRootRow packageLedger :
      BHist} :
    UnaryHistory fieldPacket ->
      UnaryHistory polynomialPacket ->
        PolynomialSingletonCarrier minimalPolynomial ->
          UnaryHistory derivativeWitness ->
            Cont minimalPolynomial derivativeWitness simpleRootRow ->
              Cont fieldPacket polynomialPacket packageLedger ->
                UnaryHistory simpleRootRow ∧
                  hsame simpleRootRow (append minimalPolynomial derivativeWitness) ∧
                    hsame packageLedger (append fieldPacket polynomialPacket) := by
  intro _ _ minimalCarrier derivativeUnary simpleRootCont packageCont
  have minimalUnary : UnaryHistory minimalPolynomial := by
    cases minimalCarrier
    exact unary_empty
  constructor
  · exact unary_cont_closed minimalUnary derivativeUnary simpleRootCont
  · constructor
    · exact simpleRootCont
    · exact packageCont

end BEDC.Derived.SeparableExtUp
