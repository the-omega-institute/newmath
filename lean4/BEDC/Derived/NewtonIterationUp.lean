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

def NewtonIterationCarrier
    (derivativeSource banachSource point derivative inverseRow nextStep derivativeLedger
      banachLedger stepLedger : BHist) :
    Prop :=
  Cont derivativeSource banachSource derivativeLedger ∧ UnaryHistory point ∧
    UnaryHistory derivative ∧ UnaryHistory inverseRow ∧ UnaryHistory nextStep ∧
      Cont derivativeLedger point derivative ∧ Cont derivative inverseRow stepLedger ∧
        Cont point stepLedger nextStep ∧ Cont derivativeLedger stepLedger banachLedger

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

theorem NewtonIterationBHistCarrier_finite_step_concatenation_closure
    {derivative banach x0 derivativeRow1 inverse1 x1 ledger1 provenance1 endpoint1
      y1 derivativeRow2 inverse2 x2 ledger2 provenance2 endpoint2 spliceLedger
      combinedEndpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach x0 derivativeRow1 inverse1 x1 ledger1
        provenance1 endpoint1 ->
      NewtonIterationBHistCarrier derivative banach y1 derivativeRow2 inverse2 x2 ledger2
          provenance2 endpoint2 ->
        hsame x1 y1 ->
          Cont endpoint1 endpoint2 spliceLedger ->
            Cont provenance1 spliceLedger combinedEndpoint ->
              UnaryHistory spliceLedger ∧ UnaryHistory combinedEndpoint ∧
                hsame combinedEndpoint (append provenance1 spliceLedger) := by
  intro first second sameSplice endpointSplice combinedRow
  have firstScope :=
    NewtonIterationBHistCarrier_banach_derivative_source_scope first
  have x1Unary : UnaryHistory x1 :=
    firstScope.right.right.right.right.right.right.left
  have y1Unary : UnaryHistory y1 :=
    unary_transport x1Unary sameSplice
  have endpoint1Unary : UnaryHistory endpoint1 :=
    firstScope.right.right.right.right.right.right.right.left
  have derivativeRow2Unary : UnaryHistory derivativeRow2 :=
    second.right.right.right.left
  have inverse2Unary : UnaryHistory inverse2 :=
    second.right.right.right.right.left
  have provenance2Unary : UnaryHistory provenance2 :=
    second.right.right.right.right.right.left
  have ledger2Row : Cont y1 derivativeRow2 ledger2 :=
    second.right.right.right.right.right.right.left
  have x2Row : Cont ledger2 inverse2 x2 :=
    second.right.right.right.right.right.right.right.left
  have endpoint2Row : Cont provenance2 x2 endpoint2 :=
    second.right.right.right.right.right.right.right.right
  have ledger2Unary : UnaryHistory ledger2 :=
    unary_cont_closed y1Unary derivativeRow2Unary ledger2Row
  have x2Unary : UnaryHistory x2 :=
    unary_cont_closed ledger2Unary inverse2Unary x2Row
  have endpoint2Unary : UnaryHistory endpoint2 :=
    unary_cont_closed provenance2Unary x2Unary endpoint2Row
  have provenance1Unary : UnaryHistory provenance1 :=
    first.right.right.right.right.right.left
  have spliceUnary : UnaryHistory spliceLedger :=
    unary_cont_closed endpoint1Unary endpoint2Unary endpointSplice
  have combinedUnary : UnaryHistory combinedEndpoint :=
    unary_cont_closed provenance1Unary spliceUnary combinedRow
  exact ⟨spliceUnary, combinedUnary, combinedRow⟩

theorem NewtonIterationBHistCarrier_finite_prefix_restriction
    {derivative banach point derivativeRow inverse next stepLedger provenance endpoint
      prefixLedger prefixNext prefixEndpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
        provenance endpoint ->
      Cont point derivativeRow prefixLedger ->
        Cont prefixLedger inverse prefixNext ->
          Cont provenance prefixNext prefixEndpoint ->
            NewtonIterationBHistCarrier derivative banach point derivativeRow inverse
                prefixNext prefixLedger provenance prefixEndpoint ∧
              hsame prefixLedger stepLedger ∧ hsame prefixNext next ∧
                hsame prefixEndpoint endpoint := by
  intro carrier prefixLedgerRow prefixNextRow prefixEndpointRow
  have derivativeUnary : UnaryHistory derivative :=
    carrier.left
  have banachUnary : UnaryHistory banach :=
    carrier.right.left
  have pointUnary : UnaryHistory point :=
    carrier.right.right.left
  have derivativeRowUnary : UnaryHistory derivativeRow :=
    carrier.right.right.right.left
  have inverseUnary : UnaryHistory inverse :=
    carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.left
  have originalLedgerRow : Cont point derivativeRow stepLedger :=
    carrier.right.right.right.right.right.right.left
  have originalNextRow : Cont stepLedger inverse next :=
    carrier.right.right.right.right.right.right.right.left
  have originalEndpointRow : Cont provenance next endpoint :=
    carrier.right.right.right.right.right.right.right.right
  have prefixLedgerSame : hsame prefixLedger stepLedger :=
    cont_respects_hsame (hsame_refl point) (hsame_refl derivativeRow) prefixLedgerRow
      originalLedgerRow
  have prefixNextSame : hsame prefixNext next :=
    cont_respects_hsame prefixLedgerSame (hsame_refl inverse) prefixNextRow originalNextRow
  have prefixEndpointSame : hsame prefixEndpoint endpoint :=
    cont_respects_hsame (hsame_refl provenance) prefixNextSame prefixEndpointRow
      originalEndpointRow
  have prefixCarrier :
      NewtonIterationBHistCarrier derivative banach point derivativeRow inverse prefixNext
        prefixLedger provenance prefixEndpoint :=
    And.intro derivativeUnary
      (And.intro banachUnary
        (And.intro pointUnary
          (And.intro derivativeRowUnary
            (And.intro inverseUnary
              (And.intro provenanceUnary
                (And.intro prefixLedgerRow
                  (And.intro prefixNextRow prefixEndpointRow)))))))
  exact
    And.intro prefixCarrier
      (And.intro prefixLedgerSame (And.intro prefixNextSame prefixEndpointSame))

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

theorem NewtonIterationBHistCarrier_step_endpoint_transport
    {derivative banach point point' derivativeRow derivativeRow' inverse inverse' next next'
      stepLedger stepLedger' provenance endpoint endpoint' : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
        provenance endpoint ->
      hsame point point' ->
        hsame derivativeRow derivativeRow' ->
          hsame inverse inverse' ->
            Cont point' derivativeRow' stepLedger' ->
              Cont stepLedger' inverse' next' ->
                Cont provenance next' endpoint' ->
                  NewtonIterationBHistCarrier derivative banach point' derivativeRow' inverse'
                      next' stepLedger' provenance endpoint' ∧
                    hsame stepLedger stepLedger' ∧ hsame next next' ∧
                      hsame endpoint endpoint' := by
  intro carrier samePoint sameDerivativeRow sameInverse stepLedgerRow' nextRow' endpointRow'
  have sameStepLedger : hsame stepLedger stepLedger' :=
    cont_respects_hsame samePoint sameDerivativeRow
      carrier.right.right.right.right.right.right.left stepLedgerRow'
  have sameNext : hsame next next' :=
    cont_respects_hsame sameStepLedger sameInverse
      carrier.right.right.right.right.right.right.right.left nextRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameNext
      carrier.right.right.right.right.right.right.right.right endpointRow'
  have transportedCarrier :
      NewtonIterationBHistCarrier derivative banach point' derivativeRow' inverse' next'
        stepLedger' provenance endpoint' :=
    ⟨carrier.left,
      carrier.right.left,
      unary_transport carrier.right.right.left samePoint,
      unary_transport carrier.right.right.right.left sameDerivativeRow,
      unary_transport carrier.right.right.right.right.left sameInverse,
      carrier.right.right.right.right.right.left,
      stepLedgerRow',
      nextRow',
      endpointRow'⟩
  exact And.intro transportedCarrier
    (And.intro sameStepLedger (And.intro sameNext sameEndpoint))

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

theorem NewtonIterationBHistCarrier_finite_step_ledger_concat_closure
    {derivative banach point derivativeRow inverse next stepLedger provenance endpoint derivative'
      banach' point' derivativeRow' inverse' next' stepLedger' provenance' endpoint'
      joined : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
      provenance endpoint ->
      NewtonIterationBHistCarrier derivative' banach' point' derivativeRow' inverse' next'
        stepLedger' provenance' endpoint' ->
        Cont endpoint endpoint' joined ->
          UnaryHistory joined ∧ hsame joined (append endpoint endpoint') := by
  intro firstCarrier secondCarrier joinedCont
  have firstScope :=
    NewtonIterationBHistCarrier_banach_derivative_source_scope firstCarrier
  have secondScope :=
    NewtonIterationBHistCarrier_banach_derivative_source_scope secondCarrier
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed firstScope.right.right.right.right.right.right.right.left
      secondScope.right.right.right.right.right.right.right.left joinedCont
  exact And.intro joinedUnary joinedCont

theorem NewtonIterationCarrier_obligation_package
    {derivativeSource banachSource point derivative inverseRow nextStep derivativeLedger
      banachLedger stepLedger derivativeSourceNext banachSourceNext pointNext derivativeNext
      inverseRowNext nextStepNext derivativeLedgerNext banachLedgerNext stepLedgerNext :
        BHist} :
    NewtonIterationCarrier derivativeSource banachSource point derivative inverseRow nextStep
        derivativeLedger banachLedger stepLedger ->
      hsame derivativeSource derivativeSourceNext ->
        hsame banachSource banachSourceNext ->
          hsame point pointNext ->
            hsame derivative derivativeNext ->
              hsame inverseRow inverseRowNext ->
                Cont derivativeSourceNext banachSourceNext derivativeLedgerNext ->
                  Cont derivativeLedgerNext pointNext derivativeNext ->
                    Cont derivativeNext inverseRowNext stepLedgerNext ->
                      Cont pointNext stepLedgerNext nextStepNext ->
                        Cont derivativeLedgerNext stepLedgerNext banachLedgerNext ->
                          NewtonIterationCarrier derivativeSourceNext banachSourceNext
                              pointNext derivativeNext inverseRowNext nextStepNext
                              derivativeLedgerNext banachLedgerNext stepLedgerNext ∧
                            hsame derivativeLedger derivativeLedgerNext ∧
                              hsame stepLedger stepLedgerNext ∧
                                hsame nextStep nextStepNext ∧
                                  hsame banachLedger banachLedgerNext := by
  intro carrier sameDerivativeSource sameBanachSource samePoint sameDerivative sameInverseRow
    sourceRows derivativeRows stepRows nextRows banachRows
  have pointUnary : UnaryHistory pointNext :=
    unary_transport carrier.right.left samePoint
  have derivativeUnary : UnaryHistory derivativeNext :=
    unary_transport carrier.right.right.left sameDerivative
  have inverseRowUnary : UnaryHistory inverseRowNext :=
    unary_transport carrier.right.right.right.left sameInverseRow
  have stepLedgerUnary : UnaryHistory stepLedgerNext :=
    unary_cont_closed derivativeUnary inverseRowUnary stepRows
  have nextStepUnary : UnaryHistory nextStepNext :=
    unary_cont_closed pointUnary stepLedgerUnary nextRows
  have sameDerivativeLedger : hsame derivativeLedger derivativeLedgerNext :=
    cont_respects_hsame sameDerivativeSource sameBanachSource carrier.left sourceRows
  have sameStepLedger : hsame stepLedger stepLedgerNext :=
    cont_respects_hsame sameDerivative sameInverseRow
      carrier.right.right.right.right.right.right.left stepRows
  have sameNextStep : hsame nextStep nextStepNext :=
    cont_respects_hsame samePoint sameStepLedger
      carrier.right.right.right.right.right.right.right.left nextRows
  have sameBanachLedger : hsame banachLedger banachLedgerNext :=
    cont_respects_hsame sameDerivativeLedger sameStepLedger
      carrier.right.right.right.right.right.right.right.right banachRows
  exact
    And.intro
      (And.intro sourceRows
        (And.intro pointUnary
          (And.intro derivativeUnary
            (And.intro inverseRowUnary
              (And.intro nextStepUnary
                (And.intro derivativeRows
                  (And.intro stepRows
                    (And.intro nextRows banachRows))))))))
      (And.intro sameDerivativeLedger
        (And.intro sameStepLedger
          (And.intro sameNextStep sameBanachLedger)))

end BEDC.Derived.NewtonIterationUp
