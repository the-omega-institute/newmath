import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
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

theorem MarkovChainTransitionCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} (token : PkgSig bundle BHist.Empty pkg) :
    let SourceSpec : BHist -> Prop := fun row =>
      exists probSource timeLedger randomVarRows lawRows transitionRows contLedger
        provenance : BHist,
        MarkovChainTransitionCarrier probSource timeLedger randomVarRows lawRows transitionRows
          contLedger provenance row bundle pkg
    SemanticNameCert SourceSpec SourceSpec SourceSpec
      (fun h k : BHist => SourceSpec h ∧ SourceSpec k ∧ hsame h k) := by
  let SourceSpec : BHist -> Prop := fun row =>
    exists probSource timeLedger randomVarRows lawRows transitionRows contLedger
      provenance : BHist,
      MarkovChainTransitionCarrier probSource timeLedger randomVarRows lawRows transitionRows
        contLedger provenance row bundle pkg
  have emptySource : SourceSpec BHist.Empty := by
    exact
      ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty,
        ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, unary_empty,
          unary_empty, unary_empty, rfl, rfl, rfl, token⟩⟩
  constructor
  · constructor
    · exact ⟨BHist.Empty, emptySource⟩
    · intro h source
      exact ⟨source, source, hsame_refl h⟩
    · intro h k classified
      exact ⟨classified.right.left, classified.left, hsame_symm classified.right.right⟩
    · intro h k r classifiedHK classifiedKR
      exact
        ⟨classifiedHK.left, classifiedKR.right.left,
          hsame_trans classifiedHK.right.right classifiedKR.right.right⟩
    · intro h k classified _source
      exact classified.right.left
  · intro h source
    exact source
  · intro h source
    exact source

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

theorem MarkovChainBHistTransitionCarrier_adjacent_transition_transport
    [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint random' law' transition'
      controw' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      hsame random random' ->
        hsame law law' ->
          hsame transition transition' ->
            Cont random' transition' controw' ->
              Cont provenance controw' endpoint' ->
                MarkovChainBHistTransitionCarrier prob random' law' transition' controw'
                    provenance endpoint' bundle pkg ∧
                  hsame controw controw' ∧ hsame endpoint endpoint' := by
  intro carrier sameRandom sameLaw sameTransition controwRow' endpointRow'
  have sameControw : hsame controw controw' :=
    cont_respects_hsame sameRandom sameTransition
      carrier.right.right.right.right.right.right.right.left controwRow'
  have oldProvenanceRow : Cont prob law provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have provenanceRow' : Cont prob law' provenance := by
    cases sameLaw
    exact oldProvenanceRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameControw
      carrier.right.right.right.right.right.right.right.right.right.left endpointRow'
  have transportedPkg : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact carrier.right.right.right.right.right.right.right.right.right.right
  have transportedCarrier :
      MarkovChainBHistTransitionCarrier prob random' law' transition' controw' provenance
        endpoint' bundle pkg :=
    ⟨carrier.left,
      unary_transport carrier.right.left sameRandom,
      unary_transport carrier.right.right.left sameLaw,
      unary_transport carrier.right.right.right.left sameTransition,
      unary_transport carrier.right.right.right.right.left sameControw,
      carrier.right.right.right.right.right.left,
      unary_transport carrier.right.right.right.right.right.right.left sameEndpoint,
      controwRow',
      provenanceRow',
      endpointRow',
      transportedPkg⟩
  exact And.intro transportedCarrier (And.intro sameControw sameEndpoint)

def MarkovChainTransitionPacket
    (source time current next law transition provenance ledger : BHist) : Prop :=
  ProbSpacePublicEventPacket source source current next law ∧ UnaryHistory time ∧
    DistributionPushforwardSourceSpec law ∧
      RandomVarTotalReadbackCertificate current next transition ∧ Cont current transition provenance ∧
        Cont provenance law ledger

theorem MarkovChainTransitionPacket_ledger_exactness
    {source time current next law transition provenance ledger : BHist} :
    MarkovChainTransitionPacket source time current next law transition provenance ledger ->
      UnaryHistory time ∧ DistributionPushforwardSourceSpec law ∧
        RandomVarTotalReadbackCertificate current next transition ∧
          Cont current transition provenance ∧ Cont provenance law ledger := by
  intro packet
  exact
    ⟨packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right⟩

theorem MarkovChainTransitionPacket_source_boundary
    {source time current next law transition provenance ledger : BHist} :
    MarkovChainTransitionPacket source time current next law transition provenance ledger ->
      ProbSpacePublicEventPacket source source current next law ∧
        DistributionPushforwardSourceSpec law ∧
          RandomVarTotalReadbackCertificate current next transition ∧
            Cont current transition provenance ∧ Cont provenance law ledger := by
  intro packet
  exact
    ⟨packet.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right⟩

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

theorem MarkovChainTransitionPacket_semantic_source_boundary
    {source time current next law transition provenance ledger : BHist} :
    MarkovChainTransitionPacket source time current next law transition provenance ledger ->
      SemanticNameCert
        (fun endpoint : BHist =>
          exists provenanceRow : BHist, exists transitionRow : BHist, exists lawRow : BHist,
            MarkovChainTransitionPacket source time current next lawRow transitionRow
              provenanceRow endpoint)
        (fun endpoint : BHist =>
          exists provenanceRow : BHist, exists transitionRow : BHist, exists lawRow : BHist,
            MarkovChainTransitionPacket source time current next lawRow transitionRow
              provenanceRow endpoint)
        (fun endpoint : BHist =>
          exists provenanceRow : BHist, exists transitionRow : BHist, exists lawRow : BHist,
            MarkovChainTransitionPacket source time current next lawRow transitionRow
              provenanceRow endpoint)
        (fun endpoint endpoint' : BHist => hsame endpoint endpoint') := by
  intro packet
  let EndpointCarrier : BHist -> Prop :=
    fun endpoint : BHist =>
      exists provenanceRow : BHist, exists transitionRow : BHist, exists lawRow : BHist,
        MarkovChainTransitionPacket source time current next lawRow transitionRow
          provenanceRow endpoint
  have carrierWitness : exists endpoint : BHist, EndpointCarrier endpoint :=
    Exists.intro ledger
      (Exists.intro provenance (Exists.intro transition (Exists.intro law packet)))
  have carrierTransport :
      forall {endpoint endpoint' : BHist},
        hsame endpoint endpoint' -> EndpointCarrier endpoint -> EndpointCarrier endpoint' := by
    intro endpoint endpoint' sameEndpoint carrier
    cases carrier with
    | intro provenanceRow rest =>
        cases rest with
        | intro transitionRow rest =>
            cases rest with
            | intro lawRow endpointPacket =>
                have endpointCont' : Cont provenanceRow lawRow endpoint' :=
                  cont_result_hsame_transport endpointPacket.right.right.right.right.right
                    sameEndpoint
                exact Exists.intro provenanceRow
                  (Exists.intro transitionRow
                    (Exists.intro lawRow
                      (And.intro endpointPacket.left
                        (And.intro endpointPacket.right.left
                          (And.intro endpointPacket.right.right.left
                            (And.intro endpointPacket.right.right.right.left
                              (And.intro endpointPacket.right.right.right.right.left
                                endpointCont')))))))
  have core : NameCert EndpointCarrier (fun endpoint endpoint' : BHist => hsame endpoint endpoint') :=
    {
      carrier_inhabited := carrierWitness
      equiv_refl := by
        intro endpoint _carrier
        exact hsame_refl endpoint
      equiv_symm := by
        intro endpoint endpoint' sameEndpoint
        exact hsame_symm sameEndpoint
      equiv_trans := by
        intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro endpoint endpoint' sameEndpoint carrier
        exact carrierTransport sameEndpoint carrier
    }
  exact {
    core := core
    pattern_sound := by
      intro endpoint carrier
      exact carrier
    ledger_sound := by
      intro endpoint carrier
      exact carrier
  }

theorem MarkovChainTransitionPacket_splice_transport_closure
    {source time current splice law transition provenance ledger source' time' splice' next law'
      transition' provenance' ledger' transportedProvenance transportedLedger : BHist} :
    MarkovChainTransitionPacket source time current splice law transition provenance ledger ->
      MarkovChainTransitionPacket source' time' splice' next law' transition' provenance'
        ledger' ->
        hsame source source' ->
          hsame splice splice' ->
            Cont splice transition' transportedProvenance ->
              Cont transportedProvenance law' transportedLedger ->
                MarkovChainTransitionPacket source time' splice next law' transition'
                    transportedProvenance transportedLedger ∧
                  hsame provenance' transportedProvenance ∧ hsame ledger' transportedLedger := by
  intro firstPacket secondPacket sameSource sameSplice transportedProvenanceCont
    transportedLedgerCont
  have sourceRows :
      ProbSpacePublicEventPacket source source splice next law' :=
    (ProbSpacePublicEventPacket_transport_rows (hsame_symm sameSource) (hsame_symm sameSource)
      (hsame_symm sameSplice) (hsame_refl next) (hsame_refl law') secondPacket.left).left
  have readback :
      RandomVarTotalReadbackCertificate splice next transition' := {
    chosen_readback :=
      cont_hsame_transport (hsame_symm sameSplice) (hsame_refl BHist.Empty)
        (hsame_refl transition') secondPacket.right.right.right.left.chosen_readback
    carried_total_bridge :=
      cont_hsame_transport (hsame_symm sameSplice) (hsame_refl BHist.Empty)
        (hsame_refl next) secondPacket.right.right.right.left.carried_total_bridge
  }
  have sameProvenance : hsame provenance' transportedProvenance :=
    cont_respects_hsame (hsame_symm sameSplice) (hsame_refl transition')
      secondPacket.right.right.right.right.left transportedProvenanceCont
  have sameLedger : hsame ledger' transportedLedger :=
    cont_respects_hsame sameProvenance (hsame_refl law')
      secondPacket.right.right.right.right.right transportedLedgerCont
  have transportedPacket :
      MarkovChainTransitionPacket source time' splice next law' transition'
        transportedProvenance transportedLedger :=
    And.intro sourceRows
      (And.intro secondPacket.right.left
        (And.intro secondPacket.right.right.left
          (And.intro readback (And.intro transportedProvenanceCont transportedLedgerCont))))
  exact And.intro transportedPacket (And.intro sameProvenance sameLedger)

def MarkovChainTransitionLedgerSurface (ledger : BHist) : Prop :=
  ∃ source time current next law transition provenance : BHist,
    MarkovChainTransitionPacket source time current next law transition provenance ledger

theorem MarkovChainTransitionLedgerSurface_semantic_name_certificate {ledger : BHist} :
    MarkovChainTransitionLedgerSurface ledger ->
      SemanticNameCert MarkovChainTransitionLedgerSurface MarkovChainTransitionLedgerSurface
        MarkovChainTransitionLedgerSurface hsame := by
  intro surface
  have cert :
      NameCert MarkovChainTransitionLedgerSurface hsame := {
    carrier_inhabited := Exists.intro ledger surface
    equiv_refl := by
      intro row _rowSurface
      exact hsame_refl row
    equiv_symm := by
      intro row row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro row row' sameRows rowSurface
      cases rowSurface with
      | intro source rowSurface =>
          cases rowSurface with
          | intro time rowSurface =>
              cases rowSurface with
              | intro current rowSurface =>
                  cases rowSurface with
                  | intro next rowSurface =>
                      cases rowSurface with
                      | intro law rowSurface =>
                          cases rowSurface with
                          | intro transition rowSurface =>
                              cases rowSurface with
                              | intro provenance packet =>
                                  have ledgerRow' : Cont provenance law row' :=
                                    cont_result_hsame_transport
                                      packet.right.right.right.right.right sameRows
                                  exact Exists.intro source
                                    (Exists.intro time
                                      (Exists.intro current
                                        (Exists.intro next
                                          (Exists.intro law
                                            (Exists.intro transition
                                              (Exists.intro provenance
                                                (And.intro packet.left
                                                  (And.intro packet.right.left
                                                    (And.intro packet.right.right.left
                                                      (And.intro packet.right.right.right.left
                                                        (And.intro
                                                          packet.right.right.right.right.left
                                                          ledgerRow')))))))))))
  }
  exact {
    core := cert
    pattern_sound := by
      intro _row rowSurface
      exact rowSurface
    ledger_sound := by
      intro _row rowSurface
      exact rowSurface
  }

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

theorem MarkovChainTransitionPacket_dependency_unary_closure
    {source time current next law transition provenance ledger : BHist} :
    MarkovChainTransitionPacket source time current next law transition provenance ledger ->
      UnaryHistory law ∧ UnaryHistory transition ∧ UnaryHistory provenance ∧ UnaryHistory ledger := by
  intro packet
  have lawBounds :
      hsame law source ∧ UnaryHistory law ∧ Cont current next law ∧
        BEDC.Derived.PreorderUp.PreorderPrefixLE current source :=
    ProbSpacePublicEventPacket_normalization_bounds packet.left
  have transitionExact :
      UnaryHistory transition ∧ hsame transition next :=
    RandomVarTotalReadbackCertificate_total_event_preimage_exactness packet.left.right.left
      packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left.left transitionExact.left packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary lawBounds.right.left packet.right.right.right.right.right
  exact And.intro lawBounds.right.left
    (And.intro transitionExact.left (And.intro provenanceUnary ledgerUnary))

theorem MarkovChainBHistTransitionCarrier_source_boundary
    [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      UnaryHistory prob ∧ UnaryHistory random ∧ UnaryHistory law ∧
        UnaryHistory transition ∧ Cont random transition controw ∧
          Cont prob law provenance ∧ Cont provenance controw endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem MarkovChainBHistTransitionCarrier_probspace_randomvar_source_boundary
    [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint ∧ UnaryHistory h)
        (fun h : BHist =>
          hsame h endpoint ∧ Cont random transition controw ∧ Cont prob law provenance ∧
            Cont provenance controw endpoint)
        hsame := by
  intro carrier
  have endpointUnary : UnaryHistory endpoint :=
    carrier.right.right.right.right.right.right.left
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact And.intro source (unary_transport endpointUnary (hsame_symm source))
    ledger_sound := by
      intro row source
      exact
        And.intro source
          (And.intro carrier.right.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.right.left
              carrier.right.right.right.right.right.right.right.right.right.left))
  }

theorem MarkovChainBHistTransitionCarrier_transition_concat_closure [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint transitionExtra transitionPacked
      controwPacked endpointPacked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      UnaryHistory transitionExtra ->
        Cont transition transitionExtra transitionPacked ->
          Cont random transitionPacked controwPacked ->
            Cont provenance controwPacked endpointPacked ->
              PkgSig bundle endpointPacked pkg ->
                MarkovChainBHistTransitionCarrier prob random law transitionPacked controwPacked
                    provenance endpointPacked bundle pkg ∧
                  UnaryHistory transitionPacked ∧ UnaryHistory controwPacked ∧
                    UnaryHistory endpointPacked ∧ hsame transitionPacked
                      (append transition transitionExtra) ∧
                      hsame controwPacked (append random transitionPacked) ∧
                        hsame endpointPacked (append provenance controwPacked) := by
  intro carrier transitionExtraUnary transitionPackedRow controwPackedRow endpointPackedRow
    endpointPackedSig
  have transitionPackedUnary : UnaryHistory transitionPacked :=
    unary_cont_closed carrier.right.right.right.left transitionExtraUnary transitionPackedRow
  have controwPackedUnary : UnaryHistory controwPacked :=
    unary_cont_closed carrier.right.left transitionPackedUnary controwPackedRow
  have endpointPackedUnary : UnaryHistory endpointPacked :=
    unary_cont_closed carrier.right.right.right.right.right.left controwPackedUnary
      endpointPackedRow
  have packedCarrier :
      MarkovChainBHistTransitionCarrier prob random law transitionPacked controwPacked provenance
        endpointPacked bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      transitionPackedUnary,
      controwPackedUnary,
      carrier.right.right.right.right.right.left,
      endpointPackedUnary,
      controwPackedRow,
      carrier.right.right.right.right.right.right.right.right.left,
      endpointPackedRow,
      endpointPackedSig⟩
  exact
    ⟨packedCarrier,
      transitionPackedUnary,
      controwPackedUnary,
      endpointPackedUnary,
      transitionPackedRow,
      controwPackedRow,
      endpointPackedRow⟩

theorem MarkovChainBHistTransitionCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance
            endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance
            endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          MarkovChainBHistTransitionCarrier prob random law transition controw provenance
            endpoint bundle pkg ∧ hsame row endpoint)
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

end BEDC.Derived.MarkovChainUp
