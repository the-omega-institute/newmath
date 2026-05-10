import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary

namespace BEDC.Derived.NewtonIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def NewtonIterationBHistCarrier
    (derivative banach point derivativeRow inverse next stepLedger provenance endpoint : BHist) :
    Prop :=
  UnaryHistory derivative ∧ UnaryHistory banach ∧ UnaryHistory point ∧
    UnaryHistory derivativeRow ∧ UnaryHistory inverse ∧ UnaryHistory provenance ∧
      Cont point derivativeRow stepLedger ∧ Cont stepLedger inverse next ∧
        Cont provenance next endpoint

theorem NewtonIterationBHistCarrier_banach_derivative_source_scope
    {derivative banach point derivativeRow inverse next stepLedger provenance endpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
      provenance endpoint ->
      UnaryHistory derivative ∧ UnaryHistory banach ∧ UnaryHistory point ∧
        UnaryHistory derivativeRow ∧ UnaryHistory inverse ∧ UnaryHistory stepLedger ∧
          UnaryHistory next ∧ UnaryHistory endpoint ∧ Cont point derivativeRow stepLedger ∧
            Cont stepLedger inverse next ∧ Cont provenance next endpoint ∧
              hsame endpoint (append provenance next) := by
  intro carrier
  have derivativeUnary : UnaryHistory derivative := carrier.left
  have banachUnary : UnaryHistory banach := carrier.right.left
  have pointUnary : UnaryHistory point := carrier.right.right.left
  have derivativeRowUnary : UnaryHistory derivativeRow := carrier.right.right.right.left
  have inverseUnary : UnaryHistory inverse := carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.right.right.left
  have pointDerivative : Cont point derivativeRow stepLedger :=
    carrier.right.right.right.right.right.right.left
  have stepInverse : Cont stepLedger inverse next :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceNext : Cont provenance next endpoint :=
    carrier.right.right.right.right.right.right.right.right
  have stepLedgerUnary : UnaryHistory stepLedger :=
    unary_cont_closed pointUnary derivativeRowUnary pointDerivative
  have nextUnary : UnaryHistory next :=
    unary_cont_closed stepLedgerUnary inverseUnary stepInverse
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary nextUnary provenanceNext
  exact
    ⟨derivativeUnary,
      banachUnary,
      pointUnary,
      derivativeRowUnary,
      inverseUnary,
      stepLedgerUnary,
      nextUnary,
      endpointUnary,
      pointDerivative,
      stepInverse,
      provenanceNext,
      provenanceNext⟩

theorem NewtonIterationStep_stability
    {derivative derivative' banach banach' point point' inverse inverse' next next' step
      step' ledger ledger' : BHist} :
    UnaryHistory derivative -> UnaryHistory banach -> UnaryHistory point ->
      UnaryHistory inverse -> hsame derivative derivative' -> hsame banach banach' ->
        hsame point point' -> hsame inverse inverse' -> Cont derivative point step ->
          Cont derivative' point' step' -> Cont step inverse ledger ->
            Cont step' inverse' ledger' -> Cont ledger banach next ->
              Cont ledger' banach' next' ->
                UnaryHistory step' ∧ UnaryHistory ledger' ∧ UnaryHistory next' ∧
                  hsame step step' ∧ hsame ledger ledger' ∧ hsame next next' := by
  intro derivativeUnary banachUnary pointUnary inverseUnary sameDerivative sameBanach samePoint
    sameInverse stepCont stepCont' ledgerCont ledgerCont' nextCont nextCont'
  have derivativeUnary' : UnaryHistory derivative' :=
    unary_transport derivativeUnary sameDerivative
  have pointUnary' : UnaryHistory point' :=
    unary_transport pointUnary samePoint
  have inverseUnary' : UnaryHistory inverse' :=
    unary_transport inverseUnary sameInverse
  have banachUnary' : UnaryHistory banach' :=
    unary_transport banachUnary sameBanach
  have stepUnary' : UnaryHistory step' :=
    unary_cont_closed derivativeUnary' pointUnary' stepCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed stepUnary' inverseUnary' ledgerCont'
  have nextUnary' : UnaryHistory next' :=
    unary_cont_closed ledgerUnary' banachUnary' nextCont'
  have sameStep : hsame step step' :=
    cont_respects_hsame sameDerivative samePoint stepCont stepCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameStep sameInverse ledgerCont ledgerCont'
  have sameNext : hsame next next' :=
    cont_respects_hsame sameLedger sameBanach nextCont nextCont'
  exact And.intro stepUnary'
    (And.intro ledgerUnary'
      (And.intro nextUnary'
        (And.intro sameStep
          (And.intro sameLedger sameNext))))

theorem NewtonIterationBHistCarrier_semantic_name_certificate
    {derivative banach point derivativeRow inverse next stepLedger provenance endpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
        provenance endpoint ->
      SemanticNameCert
        (fun row : BHist =>
          NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next
            stepLedger provenance endpoint ∧ hsame row endpoint)
        (fun row : BHist =>
          NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next
            stepLedger provenance endpoint ∧ hsame row endpoint)
        (fun row : BHist =>
          NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next
            stepLedger provenance endpoint ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.NewtonIterationUp
