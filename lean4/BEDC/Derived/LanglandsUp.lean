import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LanglandsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LanglandsBHistCorrespondenceCarrier [AskSetup] [PackageSetup]
    (galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧ UnaryHistory galoisAnswer ∧
    UnaryHistory automorphicAnswer ∧ UnaryHistory provenance ∧
      Cont galoisAnswer automorphicAnswer localFactor ∧
        Cont galoisSource automorphicSource ledger ∧
          Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem LanglandsCorrespondenceCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} (token : PkgSig bundle BHist.Empty pkg) :
    let SourceSpec : BHist -> Prop := fun endpoint =>
      exists galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
        ledger : BHist,
        LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
          automorphicAnswer localFactor provenance ledger endpoint bundle pkg
    SemanticNameCert SourceSpec SourceSpec SourceSpec
      (fun h k : BHist => SourceSpec h ∧ SourceSpec k ∧ hsame h k) := by
  let SourceSpec : BHist -> Prop := fun endpoint =>
    exists galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger : BHist,
      LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg
  have emptySource : SourceSpec BHist.Empty := by
    exact
      ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty,
        ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, rfl, rfl, rfl,
          token⟩⟩
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

def LanglandsLFactorClassifier [AskSetup] [PackageSetup]
    (galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
      automorphicAnswer localFactor provenance ledger endpoint bundle pkg ∧
    hsame galoisSource galoisSource' ∧ hsame automorphicSource automorphicSource' ∧
      hsame galoisAnswer galoisAnswer' ∧ hsame automorphicAnswer automorphicAnswer' ∧
        hsame provenance provenance' ∧ PkgSig bundle endpoint' pkg

def LanglandsCorrespondenceLedger [AskSetup] [PackageSetup]
    (galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor packageLedger
      observationLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧ UnaryHistory galoisAnswer ∧
    UnaryHistory automorphicAnswer ∧ UnaryHistory localFactor ∧
      Cont galoisSource automorphicSource packageLedger ∧
        Cont galoisAnswer automorphicAnswer localFactor ∧
          Cont packageLedger localFactor observationLedger ∧
            Cont observationLedger localFactor endpoint ∧ PkgSig bundle endpoint pkg

theorem LanglandsLFactorClassifier_observed_packet_rows [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' packageLedger' observationLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer automorphicAnswer
        localFactor provenance ledger endpoint galoisSource' automorphicSource'
        galoisAnswer' automorphicAnswer' localFactor' provenance' packageLedger' endpoint'
        bundle pkg ->
      Cont galoisAnswer' automorphicAnswer' localFactor' ->
        Cont galoisSource' automorphicSource' packageLedger' ->
          Cont packageLedger' localFactor' observationLedger' ->
            Cont observationLedger' localFactor' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                LanglandsCorrespondenceLedger galoisSource' automorphicSource' galoisAnswer'
                    automorphicAnswer' localFactor' packageLedger' observationLedger' endpoint'
                    bundle pkg ∧
                  hsame localFactor localFactor' ∧ hsame ledger packageLedger' := by
  intro classified localFactorRow' packageLedgerRow' observationLedgerRow' endpointRow'
    packageSig'
  have carrier := classified.left
  have sameGaloisSource := classified.right.left
  have sameAutomorphicSource := classified.right.right.left
  have sameGaloisAnswer := classified.right.right.right.left
  have sameAutomorphicAnswer := classified.right.right.right.right.left
  have sameLocalFactor : hsame localFactor localFactor' :=
    cont_respects_hsame sameGaloisAnswer sameAutomorphicAnswer
      carrier.right.right.right.right.right.left localFactorRow'
  have sameLedger : hsame ledger packageLedger' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.left packageLedgerRow'
  have localFactorUnary : UnaryHistory localFactor' :=
    unary_cont_closed
      (unary_transport carrier.right.right.left sameGaloisAnswer)
      (unary_transport carrier.right.right.right.left sameAutomorphicAnswer)
      localFactorRow'
  exact
    ⟨⟨unary_transport carrier.left sameGaloisSource,
        unary_transport carrier.right.left sameAutomorphicSource,
        unary_transport carrier.right.right.left sameGaloisAnswer,
        unary_transport carrier.right.right.right.left sameAutomorphicAnswer,
        localFactorUnary,
        packageLedgerRow',
        localFactorRow',
        observationLedgerRow',
        endpointRow',
        packageSig'⟩,
      sameLocalFactor,
      sameLedger⟩

theorem LanglandsLFactorClassifier_local_factor_stability [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer automorphicAnswer
        localFactor provenance ledger endpoint galoisSource' automorphicSource' galoisAnswer'
        automorphicAnswer' localFactor' provenance' ledger' endpoint' bundle pkg ->
      Cont galoisAnswer' automorphicAnswer' localFactor' ->
        Cont galoisSource' automorphicSource' ledger' ->
          Cont provenance' ledger' endpoint' ->
            LanglandsBHistCorrespondenceCarrier galoisSource' automorphicSource'
                galoisAnswer' automorphicAnswer' localFactor' provenance' ledger' endpoint'
                bundle pkg ∧
              hsame localFactor localFactor' ∧ hsame ledger ledger' ∧
                hsame endpoint endpoint' := by
  intro classified localFactorRow' ledgerRow' endpointRow'
  have carrier := classified.left
  have sameGaloisSource := classified.right.left
  have sameAutomorphicSource := classified.right.right.left
  have sameGaloisAnswer := classified.right.right.right.left
  have sameAutomorphicAnswer := classified.right.right.right.right.left
  have sameProvenance := classified.right.right.right.right.right.left
  have pkgSig' := classified.right.right.right.right.right.right
  have sameLocalFactor : hsame localFactor localFactor' :=
    cont_respects_hsame sameGaloisAnswer sameAutomorphicAnswer
      carrier.right.right.right.right.right.left localFactorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨unary_transport carrier.left sameGaloisSource,
        unary_transport carrier.right.left sameAutomorphicSource,
        unary_transport carrier.right.right.left sameGaloisAnswer,
        unary_transport carrier.right.right.right.left sameAutomorphicAnswer,
        unary_transport carrier.right.right.right.right.left sameProvenance,
        localFactorRow', ledgerRow', endpointRow', pkgSig'⟩,
      sameLocalFactor, sameLedger, sameEndpoint⟩

theorem LanglandsLocalFactor_stability [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      hsame galoisSource galoisSource' -> hsame automorphicSource automorphicSource' ->
        hsame galoisAnswer galoisAnswer' -> hsame automorphicAnswer automorphicAnswer' ->
          hsame provenance provenance' ->
            Cont galoisAnswer' automorphicAnswer' localFactor' ->
              Cont galoisSource' automorphicSource' ledger' ->
                Cont provenance' ledger' endpoint' -> PkgSig bundle endpoint' pkg ->
                  LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
                      automorphicAnswer localFactor provenance ledger endpoint galoisSource'
                      automorphicSource' galoisAnswer' automorphicAnswer' localFactor'
                      provenance' ledger' endpoint' bundle pkg ∧
                    LanglandsBHistCorrespondenceCarrier galoisSource' automorphicSource'
                      galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
                      endpoint' bundle pkg ∧
                    hsame localFactor localFactor' ∧ hsame ledger ledger' ∧
                      hsame endpoint endpoint' := by
  intro carrier sameGaloisSource sameAutomorphicSource sameGaloisAnswer
    sameAutomorphicAnswer sameProvenance localFactorRow' ledgerRow' endpointRow' pkgSig'
  have classified : LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
      automorphicAnswer localFactor provenance ledger endpoint galoisSource'
      automorphicSource' galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
      endpoint' bundle pkg :=
    ⟨carrier, sameGaloisSource, sameAutomorphicSource, sameGaloisAnswer,
      sameAutomorphicAnswer, sameProvenance, pkgSig'⟩
  have sameLocalFactor : hsame localFactor localFactor' :=
    cont_respects_hsame sameGaloisAnswer sameAutomorphicAnswer
      carrier.right.right.right.right.right.left localFactorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  have transportedCarrier : LanglandsBHistCorrespondenceCarrier galoisSource'
      automorphicSource' galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
      endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameGaloisSource,
      unary_transport carrier.right.left sameAutomorphicSource,
      unary_transport carrier.right.right.left sameGaloisAnswer,
      unary_transport carrier.right.right.right.left sameAutomorphicAnswer,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      localFactorRow', ledgerRow', endpointRow', pkgSig'⟩
  exact
    ⟨classified, transportedCarrier, sameLocalFactor, sameLedger, sameEndpoint⟩

theorem LanglandsCorrespondenceLedger_source_certificate_scope [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor packageLedger
      observationLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsCorrespondenceLedger galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor packageLedger observationLedger endpoint bundle pkg ->
      UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧
        UnaryHistory galoisAnswer ∧ UnaryHistory automorphicAnswer ∧
          UnaryHistory localFactor ∧ Cont galoisSource automorphicSource packageLedger ∧
            Cont galoisAnswer automorphicAnswer localFactor ∧
              Cont packageLedger localFactor observationLedger ∧
                Cont observationLedger localFactor endpoint ∧ PkgSig bundle endpoint pkg := by
  intro ledger
  cases ledger with
  | intro galoisUnary rest =>
      cases rest with
      | intro automorphicUnary rest =>
          cases rest with
          | intro galoisAnswerUnary rest =>
              cases rest with
              | intro automorphicAnswerUnary rest =>
                  cases rest with
                  | intro localFactorUnary rest =>
                      cases rest with
                      | intro sourceCont rest =>
                          cases rest with
                          | intro answerCont rest =>
                              cases rest with
                              | intro observationCont rest =>
                                  cases rest with
                                  | intro endpointCont packageSig =>
                                      exact
                                        ⟨galoisUnary, automorphicUnary, galoisAnswerUnary,
                                          automorphicAnswerUnary, localFactorUnary,
                                          sourceCont, answerCont, observationCont,
                                          endpointCont, packageSig⟩

theorem LanglandsBHistCorrespondenceCarrier_generated_rows_unary [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      UnaryHistory localFactor ∧ UnaryHistory ledger ∧ UnaryHistory endpoint := by
  intro carrier
  have localFactorUnary : UnaryHistory localFactor :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.left ledgerUnary
      carrier.right.right.right.right.right.right.right.left
  exact And.intro localFactorUnary (And.intro ledgerUnary endpointUnary)

theorem LanglandsBHistCorrespondenceCarrier_source_rows [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧
        UnaryHistory galoisAnswer ∧ UnaryHistory automorphicAnswer ∧
          UnaryHistory provenance ∧ UnaryHistory localFactor ∧ UnaryHistory ledger ∧
            UnaryHistory endpoint ∧ hsame localFactor (append galoisAnswer automorphicAnswer) ∧
              hsame ledger (append galoisSource automorphicSource) ∧
                hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have localFactorUnary : UnaryHistory localFactor :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.left ledgerUnary
      carrier.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      localFactorUnary,
      ledgerUnary,
      endpointUnary,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem LanglandsBHistCorrespondenceCarrier_public_surface [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
          automorphicAnswer localFactor provenance ledger endpoint galoisSource'
          automorphicSource' galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
          endpoint' bundle pkg ->
        Cont galoisAnswer' automorphicAnswer' localFactor' ->
          Cont galoisSource' automorphicSource' ledger' ->
            Cont provenance' ledger' endpoint' ->
              UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧
                UnaryHistory galoisAnswer ∧ UnaryHistory automorphicAnswer ∧
                  UnaryHistory localFactor' ∧ UnaryHistory ledger' ∧
                    UnaryHistory endpoint' ∧ hsame localFactor localFactor' ∧
                      hsame ledger ledger' ∧ hsame endpoint endpoint' ∧
                        PkgSig bundle endpoint' pkg := by
  intro carrier classified localFactorRow' ledgerRow' endpointRow'
  have stable :=
    LanglandsLFactorClassifier_local_factor_stability classified localFactorRow' ledgerRow'
      endpointRow'
  have transportedCarrier := stable.left
  have generatedRows :=
    LanglandsBHistCorrespondenceCarrier_generated_rows_unary transportedCarrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      generatedRows.left,
      generatedRows.right.left,
      generatedRows.right.right,
      stable.right.left,
      stable.right.right.left,
      stable.right.right.right,
      transportedCarrier.right.right.right.right.right.right.right.right⟩

theorem LanglandsBHistCorrespondenceCarrier_visible_packet_boundary [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧
        UnaryHistory galoisAnswer ∧ UnaryHistory automorphicAnswer ∧
          UnaryHistory provenance ∧ UnaryHistory localFactor ∧ UnaryHistory ledger ∧
            UnaryHistory endpoint ∧ Cont galoisAnswer automorphicAnswer localFactor ∧
              Cont galoisSource automorphicSource ledger ∧ Cont provenance ledger endpoint ∧
                hsame localFactor (append galoisAnswer automorphicAnswer) ∧
                  hsame ledger (append galoisSource automorphicSource) ∧
                    hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have localFactorUnary : UnaryHistory localFactor :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.left ledgerUnary
      carrier.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      localFactorUnary,
      ledgerUnary,
      endpointUnary,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem LanglandsLFactorClassifier_endpoint_confluence [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSourceA automorphicSourceA galoisAnswerA automorphicAnswerA
      localFactorA provenanceA ledgerA endpointA galoisSourceB automorphicSourceB
      galoisAnswerB automorphicAnswerB localFactorB provenanceB ledgerB endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint galoisSourceA
        automorphicSourceA galoisAnswerA automorphicAnswerA localFactorA provenanceA ledgerA
        endpointA bundle pkg ->
      Cont galoisAnswerA automorphicAnswerA localFactorA ->
        Cont galoisSourceA automorphicSourceA ledgerA ->
          Cont provenanceA ledgerA endpointA ->
            LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
                automorphicAnswer localFactor provenance ledger endpoint galoisSourceB
                automorphicSourceB galoisAnswerB automorphicAnswerB localFactorB provenanceB
                ledgerB endpointB bundle pkg ->
              Cont galoisAnswerB automorphicAnswerB localFactorB ->
                Cont galoisSourceB automorphicSourceB ledgerB ->
                  Cont provenanceB ledgerB endpointB ->
                    hsame localFactorA localFactorB ∧ hsame ledgerA ledgerB ∧
                      hsame endpointA endpointB := by
  intro classifiedA localFactorRowA ledgerRowA endpointRowA classifiedB localFactorRowB
    ledgerRowB endpointRowB
  have branchA :=
    LanglandsLFactorClassifier_local_factor_stability classifiedA localFactorRowA ledgerRowA
      endpointRowA
  have branchB :=
    LanglandsLFactorClassifier_local_factor_stability classifiedB localFactorRowB ledgerRowB
      endpointRowB
  have sameLocalFactorA : hsame localFactor localFactorA := branchA.right.left
  have sameLedgerA : hsame ledger ledgerA := branchA.right.right.left
  have sameEndpointA : hsame endpoint endpointA := branchA.right.right.right
  have sameLocalFactorB : hsame localFactor localFactorB := branchB.right.left
  have sameLedgerB : hsame ledger ledgerB := branchB.right.right.left
  have sameEndpointB : hsame endpoint endpointB := branchB.right.right.right
  exact
    ⟨hsame_trans (hsame_symm sameLocalFactorA) sameLocalFactorB,
      hsame_trans (hsame_symm sameLedgerA) sameLedgerB,
      hsame_trans (hsame_symm sameEndpointA) sameEndpointB⟩

theorem LanglandsCorrespondenceLedger_obligation_package [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor packageLedger
      observationLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsCorrespondenceLedger galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor packageLedger observationLedger endpoint bundle pkg ->
      UnaryHistory packageLedger ∧ UnaryHistory observationLedger ∧ UnaryHistory endpoint ∧
        hsame packageLedger (append galoisSource automorphicSource) ∧
          hsame localFactor (append galoisAnswer automorphicAnswer) ∧
            hsame observationLedger (append packageLedger localFactor) ∧
              hsame endpoint (append observationLedger localFactor) ∧
                PkgSig bundle endpoint pkg := by
  intro ledger
  have packageLedgerUnary : UnaryHistory packageLedger :=
    unary_cont_closed ledger.left ledger.right.left
      ledger.right.right.right.right.right.left
  have observationLedgerUnary : UnaryHistory observationLedger :=
    unary_cont_closed packageLedgerUnary ledger.right.right.right.right.left
      ledger.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observationLedgerUnary ledger.right.right.right.right.left
      ledger.right.right.right.right.right.right.right.right.left
  exact
    ⟨packageLedgerUnary,
      observationLedgerUnary,
      endpointUnary,
      ledger.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.right.right⟩

theorem LanglandsCorrespondenceLedger_public_endpoint_boundary [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor packageLedger
      observationLedger endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsCorrespondenceLedger galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor packageLedger observationLedger endpoint bundle pkg ->
      Cont endpoint packageLedger consumer ->
        UnaryHistory packageLedger ∧ UnaryHistory observationLedger ∧ UnaryHistory endpoint ∧
          UnaryHistory consumer ∧ hsame packageLedger (append galoisSource automorphicSource) ∧
            hsame localFactor (append galoisAnswer automorphicAnswer) ∧
              hsame observationLedger (append packageLedger localFactor) ∧
                hsame endpoint (append observationLedger localFactor) ∧
                  hsame consumer (append endpoint packageLedger) ∧
                    PkgSig bundle endpoint pkg := by
  intro ledger consumerRow
  have packageRows :=
    LanglandsCorrespondenceLedger_obligation_package
      (galoisSource := galoisSource) (automorphicSource := automorphicSource)
      (galoisAnswer := galoisAnswer) (automorphicAnswer := automorphicAnswer)
      (localFactor := localFactor) (packageLedger := packageLedger)
      (observationLedger := observationLedger) (endpoint := endpoint) (bundle := bundle)
      (pkg := pkg) ledger
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed packageRows.right.right.left packageRows.left consumerRow
  exact
    ⟨packageRows.left,
      packageRows.right.left,
      packageRows.right.right.left,
      consumerUnary,
      packageRows.right.right.right.left,
      packageRows.right.right.right.right.left,
      packageRows.right.right.right.right.right.left,
      packageRows.right.right.right.right.right.right.left,
      consumerRow,
      packageRows.right.right.right.right.right.right.right⟩

theorem LanglandsCorrespondenceLedger_finite_local_factor_public_surface [AskSetup]
    [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor packageLedger
      observationLedger endpoint consumerSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsCorrespondenceLedger galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor packageLedger observationLedger endpoint bundle pkg ->
      Cont endpoint localFactor consumerSurface ->
        UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧
          UnaryHistory galoisAnswer ∧ UnaryHistory automorphicAnswer ∧
            UnaryHistory localFactor ∧ UnaryHistory packageLedger ∧
              UnaryHistory observationLedger ∧ UnaryHistory endpoint ∧
                UnaryHistory consumerSurface ∧
                  hsame packageLedger (append galoisSource automorphicSource) ∧
                    hsame localFactor (append galoisAnswer automorphicAnswer) ∧
                      hsame observationLedger (append packageLedger localFactor) ∧
                        hsame endpoint (append observationLedger localFactor) ∧
                          hsame consumerSurface (append endpoint localFactor) ∧
                            PkgSig bundle endpoint pkg := by
  intro ledger consumerRow
  have sourceScope :=
    LanglandsCorrespondenceLedger_source_certificate_scope ledger
  have packageScope :=
    LanglandsCorrespondenceLedger_obligation_package ledger
  obtain ⟨galoisUnary, automorphicUnary, galoisAnswerUnary, automorphicAnswerUnary,
    localFactorUnary, _packageRow, _factorRow, _observationRow, _endpointRow,
    _pkgSig⟩ := sourceScope
  obtain ⟨packageUnary, observationUnary, endpointUnary, samePackage, sameLocalFactor,
    sameObservation, sameEndpoint, pkgSig⟩ := packageScope
  have consumerUnary : UnaryHistory consumerSurface :=
    unary_cont_closed endpointUnary localFactorUnary consumerRow
  exact
    ⟨galoisUnary, automorphicUnary, galoisAnswerUnary, automorphicAnswerUnary,
      localFactorUnary, packageUnary, observationUnary, endpointUnary, consumerUnary,
      samePackage, sameLocalFactor, sameObservation, sameEndpoint, consumerRow, pkgSig⟩

theorem LanglandsBHistCorrespondenceCarrier_finite_local_factor_public_surface
    [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance ledger
      endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      Cont localFactor endpoint consumer ->
        UnaryHistory consumer ∧ hsame consumer (append localFactor endpoint) ∧
          PkgSig bundle endpoint pkg := by
  intro carrier consumerRow
  have localRows := LanglandsBHistCorrespondenceCarrier_generated_rows_unary carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed localRows.left localRows.right.right consumerRow
  exact ⟨consumerUnary, consumerRow, carrier.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.LanglandsUp
