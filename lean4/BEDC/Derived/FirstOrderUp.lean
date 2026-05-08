import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
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

end BEDC.Derived.FirstOrderUp
