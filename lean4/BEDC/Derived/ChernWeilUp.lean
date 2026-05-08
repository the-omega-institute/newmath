import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ChernWeilSourceEnvelope_public_rows
    {curvature derham polynomial endpoint representative classRow provenance ledger : BHist} :
    UnaryHistory curvature ->
      UnaryHistory derham ->
        UnaryHistory polynomial ->
          UnaryHistory provenance ->
            Cont curvature polynomial endpoint ->
              Cont endpoint derham representative ->
                Cont representative provenance ledger ->
                  hsame classRow ledger ->
                    UnaryHistory endpoint ∧ UnaryHistory representative ∧ UnaryHistory ledger ∧
                      hsame endpoint (append curvature polynomial) ∧
                        hsame representative (append (append curvature polynomial) derham) ∧
                          hsame ledger
                            (append (append (append curvature polynomial) derham) provenance) ∧
                            hsame classRow ledger := by
  intro curvatureUnary derhamUnary polynomialUnary provenanceUnary endpointCont representativeCont
    ledgerCont sameClassLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed curvatureUnary polynomialUnary endpointCont
  have representativeUnary : UnaryHistory representative :=
    unary_cont_closed endpointUnary derhamUnary representativeCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed representativeUnary provenanceUnary ledgerCont
  have representativeReadback : hsame representative (append (append curvature polynomial) derham) :=
    hsame_trans representativeCont
      (congrArg (fun h : BHist => append h derham) endpointCont)
  have ledgerReadback :
      hsame ledger (append (append (append curvature polynomial) derham) provenance) :=
    hsame_trans ledgerCont
      (congrArg (fun h : BHist => append h provenance) representativeReadback)
  exact And.intro endpointUnary
    (And.intro representativeUnary
      (And.intro ledgerUnary
        (And.intro endpointCont
          (And.intro representativeReadback
            (And.intro ledgerReadback sameClassLedger)))))

end BEDC.Derived.ChernWeilUp
