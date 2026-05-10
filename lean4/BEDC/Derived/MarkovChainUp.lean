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

def MarkovChainBHistTransitionCarrier [AskSetup] [PackageSetup]
    (prob time rv law kernel ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧ UnaryHistory time ∧ UnaryHistory rv ∧ UnaryHistory law ∧
    UnaryHistory kernel ∧ Cont kernel rv ledger ∧ Cont ledger law endpoint ∧
      PkgSig bundle endpoint pkg

theorem MarkovChainBHistTransitionCarrier_kernel_classifier_stability
    [AskSetup] [PackageSetup]
    {prob time rv law kernel ledger endpoint prob2 time2 rv2 law2 kernel2 ledger2
      endpoint2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob time rv law kernel ledger endpoint bundle pkg ->
      hsame prob prob2 ->
        hsame time time2 ->
          hsame rv rv2 ->
            hsame law law2 ->
              hsame kernel kernel2 ->
                Cont kernel2 rv2 ledger2 ->
                  Cont ledger2 law2 endpoint2 ->
                    PkgSig bundle endpoint2 pkg ->
                      MarkovChainBHistTransitionCarrier
                          prob2 time2 rv2 law2 kernel2 ledger2 endpoint2 bundle pkg ∧
                        hsame endpoint endpoint2 := by
  intro carrier sameProb sameTime sameRv sameLaw sameKernel kernelRow2 ledgerRow2 pkgSig2
  have probUnary2 : UnaryHistory prob2 :=
    unary_transport carrier.left sameProb
  have timeUnary2 : UnaryHistory time2 :=
    unary_transport carrier.right.left sameTime
  have rvUnary2 : UnaryHistory rv2 :=
    unary_transport carrier.right.right.left sameRv
  have lawUnary2 : UnaryHistory law2 :=
    unary_transport carrier.right.right.right.left sameLaw
  have kernelUnary2 : UnaryHistory kernel2 :=
    unary_transport carrier.right.right.right.right.left sameKernel
  have sameLedger : hsame ledger ledger2 :=
    cont_respects_hsame sameKernel sameRv carrier.right.right.right.right.right.left
      kernelRow2
  have sameEndpoint : hsame endpoint endpoint2 :=
    cont_respects_hsame sameLedger sameLaw carrier.right.right.right.right.right.right.left
      ledgerRow2
  exact
    ⟨⟨probUnary2, timeUnary2, rvUnary2, lawUnary2, kernelUnary2, kernelRow2, ledgerRow2,
        pkgSig2⟩,
      sameEndpoint⟩

theorem MarkovChainBHistTransitionCarrier_transition_ledger_exactness
    [AskSetup] [PackageSetup]
    {prob time rv law kernel ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob time rv law kernel ledger endpoint bundle pkg ->
      UnaryHistory prob ∧ UnaryHistory time ∧ UnaryHistory rv ∧ UnaryHistory law ∧
        UnaryHistory kernel ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
          Cont kernel rv ledger ∧ Cont ledger law endpoint ∧ PkgSig bundle endpoint pkg ∧
            hsame endpoint (append ledger law) := by
  intro carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.right.right.left
      carrier.right.right.left carrier.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      ledgerUnary,
      endpointUnary,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right,
      carrier.right.right.right.right.right.right.left⟩

end BEDC.Derived.MarkovChainUp
