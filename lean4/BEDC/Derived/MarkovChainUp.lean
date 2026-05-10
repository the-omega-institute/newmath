import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MarkovChainTransitionCarrier [AskSetup] [PackageSetup]
    (probSource timeLedger randomVarRows lawRows transitionRows contLedger provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory probSource ∧ UnaryHistory timeLedger ∧ UnaryHistory randomVarRows ∧
    UnaryHistory lawRows ∧ UnaryHistory transitionRows ∧ UnaryHistory contLedger ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont probSource randomVarRows lawRows ∧ Cont lawRows transitionRows contLedger ∧
          Cont provenance contLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem MarkovChainTransitionCarrier_kernel_classifier_stability [AskSetup] [PackageSetup]
    {probSource timeLedger randomVarRows lawRows transitionRows contLedger provenance endpoint
      probSource' timeLedger' randomVarRows' lawRows' transitionRows' contLedger' provenance'
      endpoint' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainTransitionCarrier probSource timeLedger randomVarRows lawRows transitionRows
        contLedger provenance endpoint bundle pkg ->
      hsame probSource probSource' ->
        hsame timeLedger timeLedger' ->
          hsame randomVarRows randomVarRows' ->
            hsame transitionRows transitionRows' ->
              hsame provenance provenance' ->
                Cont probSource' randomVarRows' lawRows' ->
                  Cont lawRows' transitionRows' contLedger' ->
                    Cont provenance' contLedger' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        MarkovChainTransitionCarrier probSource' timeLedger' randomVarRows'
                            lawRows' transitionRows' contLedger' provenance' endpoint' bundle
                            pkg ∧
                          hsame lawRows lawRows' ∧ hsame contLedger contLedger' ∧
                            hsame endpoint endpoint' := by
  intro carrier sameProbSource sameTimeLedger sameRandomVarRows sameTransitionRows
    sameProvenance lawRowsCont contLedgerCont endpointCont endpointPkg
  have probSourceUnary : UnaryHistory probSource := carrier.left
  have timeLedgerUnary : UnaryHistory timeLedger := carrier.right.left
  have randomVarRowsUnary : UnaryHistory randomVarRows := carrier.right.right.left
  have transitionRowsUnary : UnaryHistory transitionRows :=
    carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have oldLawRowsCont : Cont probSource randomVarRows lawRows :=
    carrier.right.right.right.right.right.right.right.right.left
  have oldContLedgerCont : Cont lawRows transitionRows contLedger :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have oldEndpointCont : Cont provenance contLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have probSourceUnary' : UnaryHistory probSource' :=
    unary_transport probSourceUnary sameProbSource
  have timeLedgerUnary' : UnaryHistory timeLedger' :=
    unary_transport timeLedgerUnary sameTimeLedger
  have randomVarRowsUnary' : UnaryHistory randomVarRows' :=
    unary_transport randomVarRowsUnary sameRandomVarRows
  have transitionRowsUnary' : UnaryHistory transitionRows' :=
    unary_transport transitionRowsUnary sameTransitionRows
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameLawRows : hsame lawRows lawRows' :=
    cont_respects_hsame sameProbSource sameRandomVarRows oldLawRowsCont lawRowsCont
  have lawRowsUnary' : UnaryHistory lawRows' :=
    unary_cont_closed probSourceUnary' randomVarRowsUnary' lawRowsCont
  have sameContLedger : hsame contLedger contLedger' :=
    cont_respects_hsame sameLawRows sameTransitionRows oldContLedgerCont contLedgerCont
  have contLedgerUnary' : UnaryHistory contLedger' :=
    unary_cont_closed lawRowsUnary' transitionRowsUnary' contLedgerCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameContLedger oldEndpointCont endpointCont
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' contLedgerUnary' endpointCont
  have transportedCarrier :
      MarkovChainTransitionCarrier probSource' timeLedger' randomVarRows' lawRows'
        transitionRows' contLedger' provenance' endpoint' bundle pkg :=
    And.intro probSourceUnary'
      (And.intro timeLedgerUnary'
        (And.intro randomVarRowsUnary'
          (And.intro lawRowsUnary'
            (And.intro transitionRowsUnary'
              (And.intro contLedgerUnary'
                (And.intro provenanceUnary'
                  (And.intro endpointUnary'
                    (And.intro lawRowsCont
                      (And.intro contLedgerCont
                        (And.intro endpointCont endpointPkg))))))))))
  exact And.intro transportedCarrier
    (And.intro sameLawRows (And.intro sameContLedger sameEndpoint))

end BEDC.Derived.MarkovChainUp
