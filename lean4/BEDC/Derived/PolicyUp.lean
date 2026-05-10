import BEDC.Derived.PolicyUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolicyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem PolicyUp_taste_gate_source_scope [AskSetup] [PackageSetup]
    {belief markov randomvar estimator decision ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolicyActionLedgerCarrier belief markov randomvar estimator decision ledger provenance
        endpoint bundle pkg ->
      (exists sourceLedger actionLedger : BHist,
        Cont belief markov sourceLedger ∧ Cont sourceLedger estimator actionLedger ∧
          hsame sourceLedger ledger ∧ hsame actionLedger provenance) ∧
        (exists endpoint' : BHist,
          Cont provenance decision endpoint' ∧ hsame endpoint endpoint' ∧
            PkgSig bundle endpoint' pkg) := by
  intro carrier
  exact
    ⟨⟨ledger,
        provenance,
        carrier.right.right.right.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.right.right.right.left,
        hsame_refl ledger,
        hsame_refl provenance⟩,
      ⟨endpoint,
        carrier.right.right.right.right.right.right.right.right.right.right.left,
        hsame_refl endpoint,
        carrier.right.right.right.right.right.right.right.right.right.right.right⟩⟩

theorem PolicyActionLedgerCarrier_action_classifier_stability [AskSetup] [PackageSetup]
    {belief markov randomvar estimator decision ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolicyActionLedgerCarrier belief markov randomvar estimator decision ledger provenance endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun h k : BHist =>
            hsame h k ∧
              (exists ledger' provenance' : BHist,
                Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                  Cont provenance' decision k ∧ PkgSig bundle k pkg)) ∧
        Cont belief markov ledger ∧ Cont ledger estimator provenance ∧
          Cont provenance decision endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSource :
      exists ledger' provenance' : BHist,
        Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
          Cont provenance' decision endpoint ∧ PkgSig bundle endpoint pkg :=
    Exists.intro ledger
      (Exists.intro provenance
        (And.intro carrier.right.right.right.right.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
              carrier.right.right.right.right.right.right.right.right.right.right.right))))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            exists ledger' provenance' : BHist,
              Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                Cont provenance' decision row ∧ PkgSig bundle row pkg)
          (fun h k : BHist =>
            hsame h k ∧
              (exists ledger' provenance' : BHist,
                Cont belief markov ledger' ∧ Cont ledger' estimator provenance' ∧
                  Cont provenance' decision k ∧ PkgSig bundle k pkg)) :=
    {
      core := {
        carrier_inhabited := Exists.intro endpoint endpointSource
        equiv_refl := by
          intro h source
          exact And.intro (hsame_refl h) source
        equiv_symm := by
          intro h k classified
          cases classified with
          | intro sameHK sourceK =>
              cases sameHK
              exact And.intro (hsame_refl h) sourceK
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro (hsame_trans classifiedHK.left classifiedKR.left) classifiedKR.right
        carrier_respects_equiv := by
          intro h k classified _sourceH
          exact classified.right
      }
      pattern_sound := by
        intro _h source
        exact source
      ledger_sound := by
        intro _h source
        exact source
    }
  exact And.intro cert
    (And.intro carrier.right.right.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
          carrier.right.right.right.right.right.right.right.right.right.right.right)))

theorem PolicyActionLedgerCarrier_selected_action_determinacy [AskSetup] [PackageSetup]
    {belief markov randomvar estimator decisionP ledgerP provenanceP endpointP decisionQ ledgerQ
      provenanceQ endpointQ : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolicyActionLedgerCarrier belief markov randomvar estimator decisionP ledgerP provenanceP
        endpointP bundle pkg ->
      PolicyActionLedgerCarrier belief markov randomvar estimator decisionQ ledgerQ provenanceQ
        endpointQ bundle pkg ->
        hsame decisionP decisionQ ->
          hsame endpointP endpointQ := by
  intro carrierP carrierQ sameDecision
  have sameLedger : hsame ledgerP ledgerQ :=
    cont_respects_hsame (hsame_refl belief) (hsame_refl markov)
      carrierP.right.right.right.right.right.right.right.right.left
      carrierQ.right.right.right.right.right.right.right.right.left
  have sameProvenance : hsame provenanceP provenanceQ :=
    cont_respects_hsame sameLedger (hsame_refl estimator)
      carrierP.right.right.right.right.right.right.right.right.right.left
      carrierQ.right.right.right.right.right.right.right.right.right.left
  exact
    cont_respects_hsame sameProvenance sameDecision
      carrierP.right.right.right.right.right.right.right.right.right.right.left
      carrierQ.right.right.right.right.right.right.right.right.right.right.left

end BEDC.Derived.PolicyUp
