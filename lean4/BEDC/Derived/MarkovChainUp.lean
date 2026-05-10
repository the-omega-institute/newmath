import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Derived.ProbSpaceUp
import BEDC.Derived.DistributionUp
import BEDC.Derived.RandomVarUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.Derived.ProbSpaceUp
open BEDC.Derived.DistributionUp
open BEDC.Derived.RandomVarUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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
    (prob random law transition controw provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧ UnaryHistory random ∧ UnaryHistory law ∧ UnaryHistory transition ∧
    UnaryHistory controw ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont random transition controw ∧ Cont prob law provenance ∧
        Cont provenance controw endpoint ∧ PkgSig bundle endpoint pkg

theorem MarkovChainKernelClassifier_stability [AskSetup] [PackageSetup]
    {prob prob' random random' law law' transition transition' controw controw'
      provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      hsame prob prob' -> hsame random random' -> hsame law law' ->
        hsame transition transition' -> hsame provenance provenance' ->
          Cont random' transition' controw' -> Cont prob' law' provenance' ->
            Cont provenance' controw' endpoint' -> PkgSig bundle endpoint' pkg ->
              MarkovChainBHistTransitionCarrier prob' random' law' transition' controw'
                  provenance' endpoint' bundle pkg ∧
                hsame controw controw' ∧ hsame endpoint endpoint' := by
  intro carrier sameProb sameRandom sameLaw sameTransition sameProvenance controwRow'
    provenanceRow' endpointRow' pkgSig'
  have sameControw : hsame controw controw' :=
    cont_respects_hsame sameRandom sameTransition
      carrier.right.right.right.right.right.right.right.left controwRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameControw
      carrier.right.right.right.right.right.right.right.right.right.left endpointRow'
  have transportedCarrier :
      MarkovChainBHistTransitionCarrier prob' random' law' transition' controw' provenance'
        endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameProb,
      unary_transport carrier.right.left sameRandom,
      unary_transport carrier.right.right.left sameLaw,
      unary_transport carrier.right.right.right.left sameTransition,
      unary_transport carrier.right.right.right.right.left sameControw,
      unary_transport carrier.right.right.right.right.right.left sameProvenance,
      unary_transport carrier.right.right.right.right.right.right.left sameEndpoint,
      controwRow',
      provenanceRow',
      endpointRow',
      pkgSig'⟩
  exact And.intro transportedCarrier (And.intro sameControw sameEndpoint)

theorem MarkovChainKernelClassifier_endpoint_confluence [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint probA randomA lawA transitionA
      controwA provenanceA endpointA probB randomB lawB transitionB controwB provenanceB
      endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      hsame prob probA ->
        hsame random randomA ->
          hsame law lawA ->
            hsame transition transitionA ->
              hsame provenance provenanceA ->
                Cont randomA transitionA controwA ->
                  Cont probA lawA provenanceA ->
                    Cont provenanceA controwA endpointA ->
                      PkgSig bundle endpointA pkg ->
                        hsame prob probB ->
                          hsame random randomB ->
                            hsame law lawB ->
                              hsame transition transitionB ->
                                hsame provenance provenanceB ->
                                  Cont randomB transitionB controwB ->
                                    Cont probB lawB provenanceB ->
                                      Cont provenanceB controwB endpointB ->
                                        PkgSig bundle endpointB pkg ->
                                          hsame controwA controwB ∧
                                            hsame endpointA endpointB := by
  intro carrier sameProbA sameRandomA sameLawA sameTransitionA sameProvenanceA controwRowA
    provenanceRowA endpointRowA pkgSigA sameProbB sameRandomB sameLawB sameTransitionB
    sameProvenanceB controwRowB provenanceRowB endpointRowB pkgSigB
  have branchA :=
    MarkovChainKernelClassifier_stability carrier sameProbA sameRandomA sameLawA
      sameTransitionA sameProvenanceA controwRowA provenanceRowA endpointRowA pkgSigA
  have branchB :=
    MarkovChainKernelClassifier_stability carrier sameProbB sameRandomB sameLawB
      sameTransitionB sameProvenanceB controwRowB provenanceRowB endpointRowB pkgSigB
  have sameControwA : hsame controw controwA := branchA.right.left
  have sameEndpointA : hsame endpoint endpointA := branchA.right.right
  have sameControwB : hsame controw controwB := branchB.right.left
  have sameEndpointB : hsame endpoint endpointB := branchB.right.right
  exact
    ⟨hsame_trans (hsame_symm sameControwA) sameControwB,
      hsame_trans (hsame_symm sameEndpointA) sameEndpointB⟩

def MarkovChainTransitionPacket
    (source time current next law transition provenance ledger : BHist) : Prop :=
  ProbSpacePublicEventPacket source source current next law ∧ UnaryHistory time ∧
    DistributionPushforwardSourceSpec law ∧
      RandomVarTotalReadbackCertificate current next transition ∧ Cont current transition provenance ∧
        Cont provenance law ledger

theorem MarkovChainTransitionPacket_kernel_classifier_stability
    {source time current next law transition provenance ledger source' time' current' next'
      law' transition' provenance' ledger' : BHist} :
    MarkovChainTransitionPacket source time current next law transition provenance ledger ->
      hsame source source' -> hsame time time' -> hsame current current' -> hsame next next' ->
        hsame law law' -> hsame transition transition' -> Cont current' transition' provenance' ->
          Cont provenance' law' ledger' ->
            MarkovChainTransitionPacket source' time' current' next' law' transition' provenance'
                ledger' ∧
              hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro packet sameSource sameTime sameCurrent sameNext sameLaw sameTransition
  intro transportedProvenance transportedLedger
  have sourceRows :=
    ProbSpacePublicEventPacket_transport_rows sameSource sameSource sameCurrent sameNext sameLaw
      packet.left
  have timeUnary : UnaryHistory time' :=
    unary_transport packet.right.left sameTime
  have lawSource' : DistributionPushforwardSourceSpec law' :=
    BEDC.FKernel.NameCert.NameCert.carrier_respects_equiv
      DistributionPushforwardCarrier_semantic_name_certificate.core sameLaw packet.right.right.left
  have readback' : RandomVarTotalReadbackCertificate current' next' transition' := {
    chosen_readback :=
      cont_hsame_transport sameCurrent (hsame_refl BHist.Empty) sameTransition
        packet.right.right.right.left.chosen_readback
    carried_total_bridge :=
      cont_hsame_transport sameCurrent (hsame_refl BHist.Empty) sameNext
        packet.right.right.right.left.carried_total_bridge
  }
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameCurrent sameTransition packet.right.right.right.right.left
      transportedProvenance
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance sameLaw packet.right.right.right.right.right
      transportedLedger
  have transportedPacket :
      MarkovChainTransitionPacket source' time' current' next' law' transition' provenance'
        ledger' :=
    And.intro sourceRows.left
      (And.intro timeUnary
        (And.intro lawSource'
          (And.intro readback' (And.intro transportedProvenance transportedLedger))))
  exact And.intro transportedPacket (And.intro sameProvenance sameLedger)

theorem MarkovChainBHistTransitionCarrier_transition_ledger_exactness
    [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      UnaryHistory prob ∧ UnaryHistory random ∧ UnaryHistory law ∧
        UnaryHistory transition ∧ UnaryHistory controw ∧ UnaryHistory provenance ∧
          UnaryHistory endpoint ∧ Cont random transition controw ∧
            Cont prob law provenance ∧ Cont provenance controw endpoint ∧
              PkgSig bundle endpoint pkg ∧ hsame endpoint (append provenance controw) := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right,
      carrier.right.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.MarkovChainUp
