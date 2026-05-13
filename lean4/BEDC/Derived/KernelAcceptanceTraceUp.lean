import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KernelAcceptanceTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KernelAcceptanceTraceCarrier [AskSetup] [PackageSetup]
    (candidate ty classifier stamp env ledger transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory candidate ∧ UnaryHistory ty ∧ UnaryHistory classifier ∧
    UnaryHistory stamp ∧ UnaryHistory env ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont candidate ty classifier ∧ Cont classifier stamp env ∧
          Cont env ledger route ∧ hsame endpointLedger transport ∧
            hsame endpointLedger ledger ∧ PkgSig bundle endpointLedger pkg
where
  endpointLedger : BHist := append route cert

theorem KernelAcceptanceTraceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {candidate ty classifier stamp env ledger transport route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport route
        provenance cert bundle pkg →
      Cont route cert endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport
                  route provenance cert bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row ledger)
              (fun row : BHist => hsame row ledger ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory candidate ∧ UnaryHistory ty ∧ UnaryHistory classifier ∧
              UnaryHistory stamp ∧ UnaryHistory env ∧ UnaryHistory ledger ∧
                UnaryHistory endpoint ∧ Cont candidate ty classifier ∧
                  Cont classifier stamp env ∧ Cont env ledger route ∧
                    Cont route cert endpoint := by
  -- BEDC touchpoint anchor: BHist KernelAcceptanceTraceCarrier hsame SemanticNameCert
  intro carrierData endpointRoute packageRow
  have carrier := carrierData
  obtain ⟨candidateUnary, tyUnary, classifierUnary, stampUnary, envUnary, ledgerUnary,
    _transportUnary, routeUnary, _provenanceUnary, certUnary, candidateTyClassifier,
    classifierStampEnv, envLedgerRoute, _transportSame, endpointLedgerSame, _endpointPackage⟩ :=
      carrierData
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary certUnary endpointRoute
  have endpointSameLedger : hsame endpoint ledger := by
    cases endpointRoute
    exact endpointLedgerSame
  have certSurface :
      SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport route
              provenance cert bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle endpoint pkg)
          hsame := {
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact hsame_trans sourceRow.right endpointSameLedger
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.right endpointSameLedger) packageRow
  }
  exact
    And.intro certSurface
      (And.intro candidateUnary
        (And.intro tyUnary
          (And.intro classifierUnary
            (And.intro stampUnary
              (And.intro envUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro candidateTyClassifier
                      (And.intro classifierStampEnv
                        (And.intro envLedgerRoute endpointRoute))))))))))

end BEDC.Derived.KernelAcceptanceTraceUp
