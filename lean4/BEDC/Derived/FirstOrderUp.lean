import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary.Commutativity
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FirstOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def FirstOrderBHistSyntaxCarrier [AskSetup] [PackageSetup]
    (symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symbolSource ∧
    UnaryHistory treeSource ∧
      UnaryHistory variableLedger ∧
        UnaryHistory relationSymbol ∧
          UnaryHistory functionSymbol ∧
            Cont treeSource variableLedger treeEndpoint ∧
              Cont treeEndpoint relationSymbol formulaEndpoint ∧
                SigRel bundle formulaEndpoint provenance ∧
                  PkgSig bundle provenance pkg

def FirstOrderBHistSatisfactionCarrier [AskSetup] [PackageSetup]
    (formulaEndpoint modelSource result provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory formulaEndpoint ∧ UnaryHistory modelSource ∧ UnaryHistory result ∧
    Cont formulaEndpoint modelSource result ∧ SigRel bundle result provenance ∧
      PkgSig bundle provenance pkg

theorem FirstOrderBHistSyntaxCarrier_endpoint_unary [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
      treeEndpoint formulaEndpoint provenance bundle pkg ->
        UnaryHistory treeEndpoint ∧ UnaryHistory formulaEndpoint := by
  intro carrier
  have treeEndpointUnary : UnaryHistory treeEndpoint :=
    unary_cont_closed carrier.right.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have formulaEndpointUnary : UnaryHistory formulaEndpoint :=
    unary_cont_closed treeEndpointUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  exact And.intro treeEndpointUnary formulaEndpointUnary

theorem FirstOrderBHistSyntaxCarrier_classifier_transport_obligation [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance relationSymbol' functionSymbol' formulaEndpoint' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
      treeEndpoint formulaEndpoint provenance bundle pkg ->
        hsame relationSymbol relationSymbol' ->
          hsame functionSymbol functionSymbol' ->
            hsame formulaEndpoint formulaEndpoint' ->
              Cont treeEndpoint relationSymbol' formulaEndpoint' ->
                SigRel bundle formulaEndpoint' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger
                      relationSymbol' functionSymbol' treeEndpoint formulaEndpoint' provenance'
                      bundle pkg := by
  intro carrier sameRelation sameFunction _ targetCont targetSig targetPkg
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro (unary_transport carrier.right.right.right.left sameRelation)
          (And.intro (unary_transport carrier.right.right.right.right.left sameFunction)
            (And.intro carrier.right.right.right.right.right.left
              (And.intro targetCont
                (And.intro targetSig targetPkg)))))))

theorem FirstOrderBHistSyntaxCarrier_formula_carrier_obligation [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol
      functionSymbol treeEndpoint formulaEndpoint provenance bundle pkg ->
        UnaryHistory symbolSource ∧
          UnaryHistory treeSource ∧
            UnaryHistory relationSymbol ∧
              UnaryHistory functionSymbol ∧
                UnaryHistory formulaEndpoint ∧
                  SigRel bundle formulaEndpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have endpointUnary :=
    FirstOrderBHistSyntaxCarrier_endpoint_unary
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (bundle := bundle) (pkg := pkg) carrier
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
               (And.intro endpointUnary.right
                 (And.intro carrier.right.right.right.right.right.right.right.left
                   carrier.right.right.right.right.right.right.right.right)))))

theorem FirstOrderBHistSyntaxCarrier_deduction_endpoint_exactness [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance deductionStep conclusion conclusionProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint provenance bundle pkg ->
      UnaryHistory deductionStep ->
        Cont formulaEndpoint deductionStep conclusion ->
          SigRel bundle conclusion conclusionProvenance ->
            PkgSig bundle conclusionProvenance pkg ->
              UnaryHistory formulaEndpoint ∧ UnaryHistory conclusion ∧
                hsame conclusion (append formulaEndpoint deductionStep) ∧
                  SigRel bundle conclusion conclusionProvenance ∧
                    PkgSig bundle conclusionProvenance pkg := by
  intro carrier deductionStepUnary conclusionRow conclusionSig conclusionPkg
  have endpointUnary :=
    FirstOrderBHistSyntaxCarrier_endpoint_unary
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (bundle := bundle) (pkg := pkg) carrier
  have conclusionUnary : UnaryHistory conclusion :=
    unary_cont_closed endpointUnary.right deductionStepUnary conclusionRow
  exact And.intro endpointUnary.right
    (And.intro conclusionUnary
      (And.intro conclusionRow
        (And.intro conclusionSig conclusionPkg)))

theorem FirstOrderBHistSyntaxCarrier_modeltheory_consumer_boundary [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance deductionStep conclusion conclusionProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint provenance bundle pkg ->
      UnaryHistory deductionStep ->
        Cont formulaEndpoint deductionStep conclusion ->
          SigRel bundle conclusion conclusionProvenance ->
            PkgSig bundle conclusionProvenance pkg ->
              UnaryHistory symbolSource ∧ UnaryHistory treeSource ∧
                UnaryHistory formulaEndpoint ∧ UnaryHistory conclusion ∧
                  hsame conclusion (append formulaEndpoint deductionStep) ∧
                    SigRel bundle conclusion conclusionProvenance ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle conclusionProvenance pkg := by
  intro carrier deductionStepUnary conclusionRow conclusionSig conclusionPkg
  have exactness :=
    FirstOrderBHistSyntaxCarrier_deduction_endpoint_exactness
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (deductionStep := deductionStep) (conclusion := conclusion)
      (conclusionProvenance := conclusionProvenance) (bundle := bundle) (pkg := pkg)
      carrier deductionStepUnary conclusionRow conclusionSig conclusionPkg
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro exactness.left
        (And.intro exactness.right.left
          (And.intro exactness.right.right.left
            (And.intro exactness.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right
                exactness.right.right.right.right))))))

theorem FirstOrderDeductionLedgerConcatenation_closure [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance d1 d2 joined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol
        functionSymbol treeEndpoint formulaEndpoint provenance bundle pkg ->
      UnaryHistory d1 ->
        UnaryHistory d2 ->
          Cont d1 d2 joined ->
            SigRel bundle formulaEndpoint provenance ->
              UnaryHistory joined ∧ Cont d1 d2 joined ∧
                SigRel bundle formulaEndpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier d1Unary d2Unary joinedRow formulaSig
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed d1Unary d2Unary joinedRow
  exact And.intro joinedUnary
    (And.intro joinedRow
      (And.intro formulaSig carrier.right.right.right.right.right.right.right.right))

theorem FirstOrderBHistSyntaxCarrier_deduction_soundness_ledger_obligation [AskSetup]
    [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance step1 step2 joined conclusion conclusionProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint provenance bundle pkg ->
      UnaryHistory step1 ->
        UnaryHistory step2 ->
          Cont step1 step2 joined ->
            Cont formulaEndpoint joined conclusion ->
              SigRel bundle conclusion conclusionProvenance ->
                PkgSig bundle conclusionProvenance pkg ->
                  UnaryHistory joined ∧ UnaryHistory conclusion ∧ Cont step1 step2 joined ∧
                    Cont formulaEndpoint joined conclusion ∧
                      hsame conclusion (append formulaEndpoint joined) ∧
                        SigRel bundle conclusion conclusionProvenance ∧
                          PkgSig bundle conclusionProvenance pkg := by
  intro carrier step1Unary step2Unary joinedRow conclusionRow conclusionSig conclusionPkg
  have endpointUnary :=
    FirstOrderBHistSyntaxCarrier_endpoint_unary
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (bundle := bundle) (pkg := pkg) carrier
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed step1Unary step2Unary joinedRow
  have conclusionUnary : UnaryHistory conclusion :=
    unary_cont_closed endpointUnary.right joinedUnary conclusionRow
  exact And.intro joinedUnary
    (And.intro conclusionUnary
      (And.intro joinedRow
        (And.intro conclusionRow
          (And.intro conclusionRow
            (And.intro conclusionSig conclusionPkg)))))

theorem FirstOrderBHistSyntaxCarrier_hsame_stability_obligation [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance relationSymbol' functionSymbol' treeEndpoint' formulaEndpoint'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint provenance bundle pkg ->
      hsame relationSymbol relationSymbol' ->
        hsame functionSymbol functionSymbol' ->
          Cont treeSource variableLedger treeEndpoint' ->
            Cont treeEndpoint' relationSymbol' formulaEndpoint' ->
              SigRel bundle formulaEndpoint' provenance' ->
                PkgSig bundle provenance' pkg ->
                  FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger
                      relationSymbol' functionSymbol' treeEndpoint' formulaEndpoint' provenance'
                      bundle pkg ∧
                    hsame treeEndpoint treeEndpoint' ∧ hsame formulaEndpoint formulaEndpoint' := by
  intro carrier sameRelation sameFunction treeEndpointCont' formulaEndpointCont' formulaSig' pkgSig'
  have sameTreeEndpoint : hsame treeEndpoint treeEndpoint' :=
    cont_respects_hsame (hsame_refl treeSource) (hsame_refl variableLedger)
      carrier.right.right.right.right.right.left treeEndpointCont'
  have sameFormulaEndpoint : hsame formulaEndpoint formulaEndpoint' :=
    cont_respects_hsame sameTreeEndpoint sameRelation
      carrier.right.right.right.right.right.right.left formulaEndpointCont'
  have relationUnary' : UnaryHistory relationSymbol' :=
    unary_transport carrier.right.right.right.left sameRelation
  have functionUnary' : UnaryHistory functionSymbol' :=
    unary_transport carrier.right.right.right.right.left sameFunction
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro relationUnary'
            (And.intro functionUnary'
              (And.intro treeEndpointCont'
                 (And.intro formulaEndpointCont' (And.intro formulaSig' pkgSig'))))))))
    (And.intro sameTreeEndpoint sameFormulaEndpoint)

theorem FirstOrderBHistSatisfactionCarrier_soundness_transport_row [AskSetup] [PackageSetup]
    {symbolSource treeSource variableLedger relationSymbol functionSymbol treeEndpoint
      formulaEndpoint provenance modelSource premiseResult premiseProvenance deductionStep
      conclusion conclusionResult conclusionProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FirstOrderBHistSyntaxCarrier symbolSource treeSource variableLedger relationSymbol functionSymbol
        treeEndpoint formulaEndpoint provenance bundle pkg ->
      FirstOrderBHistSatisfactionCarrier formulaEndpoint modelSource premiseResult
        premiseProvenance bundle pkg ->
        UnaryHistory deductionStep ->
          Cont formulaEndpoint deductionStep conclusion ->
            Cont premiseResult deductionStep conclusionResult ->
              SigRel bundle conclusionResult conclusionProvenance ->
                PkgSig bundle conclusionProvenance pkg ->
                  FirstOrderBHistSatisfactionCarrier conclusion modelSource conclusionResult
                      conclusionProvenance bundle pkg ∧
                    hsame conclusion (append formulaEndpoint deductionStep) ∧
                      hsame conclusionResult (append premiseResult deductionStep) ∧
                        PkgSig bundle provenance pkg := by
  intro syntaxCarrier satisfactionCarrier deductionUnary conclusionRow resultRow conclusionSig
    conclusionPkg
  have endpointUnary :=
    FirstOrderBHistSyntaxCarrier_endpoint_unary
      (symbolSource := symbolSource) (treeSource := treeSource)
      (variableLedger := variableLedger) (relationSymbol := relationSymbol)
      (functionSymbol := functionSymbol) (treeEndpoint := treeEndpoint)
      (formulaEndpoint := formulaEndpoint) (provenance := provenance)
      (bundle := bundle) (pkg := pkg) syntaxCarrier
  have formulaUnary : UnaryHistory formulaEndpoint := endpointUnary.right
  have modelUnary : UnaryHistory modelSource := satisfactionCarrier.right.left
  have premiseResultUnary : UnaryHistory premiseResult := satisfactionCarrier.right.right.left
  have premiseRow : Cont formulaEndpoint modelSource premiseResult :=
    satisfactionCarrier.right.right.right.left
  have conclusionUnary : UnaryHistory conclusion :=
    unary_cont_closed formulaUnary deductionUnary conclusionRow
  have conclusionResultUnary : UnaryHistory conclusionResult :=
    unary_cont_closed premiseResultUnary deductionUnary resultRow
  have resultAsFormulaModelDeduction :
      conclusionResult = append (append formulaEndpoint modelSource) deductionStep :=
    resultRow.trans (congrArg (fun h => append h deductionStep) premiseRow)
  have reassociateLeft :
      append (append formulaEndpoint modelSource) deductionStep =
        append formulaEndpoint (append modelSource deductionStep) :=
    append_assoc formulaEndpoint modelSource deductionStep
  have commuteModelDeduction :
      append modelSource deductionStep = append deductionStep modelSource :=
    unary_append_comm modelUnary deductionUnary
  have reassociateRight :
      append formulaEndpoint (append deductionStep modelSource) =
        append (append formulaEndpoint deductionStep) modelSource :=
    (append_assoc formulaEndpoint deductionStep modelSource).symm
  have conclusionSubst :
      append (append formulaEndpoint deductionStep) modelSource =
        append conclusion modelSource :=
    congrArg (fun h => append h modelSource) conclusionRow.symm
  have conclusionModelRow : Cont conclusion modelSource conclusionResult :=
    resultAsFormulaModelDeduction.trans
      (reassociateLeft.trans
        ((congrArg (fun h => append formulaEndpoint h) commuteModelDeduction).trans
          (reassociateRight.trans conclusionSubst)))
  exact And.intro
    (And.intro conclusionUnary
      (And.intro modelUnary
        (And.intro conclusionResultUnary
          (And.intro conclusionModelRow
            (And.intro conclusionSig conclusionPkg)))))
    (And.intro conclusionRow
      (And.intro resultRow syntaxCarrier.right.right.right.right.right.right.right.right))

end BEDC.Derived.FirstOrderUp
