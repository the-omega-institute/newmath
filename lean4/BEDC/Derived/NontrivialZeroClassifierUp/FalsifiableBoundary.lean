import BEDC.Derived.NontrivialZeroClassifierUp.NamecertObligations

namespace BEDC.Derived.NontrivialZeroClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NontrivialZeroClassifierCarrier_falsifiable_boundary [AskSetup] [PackageSetup]
    {zero strip witness trivialLedger realPart rationalLedger transport replay provenance
      localName stripRead witnessRead trivialRead ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory zero ->
      UnaryHistory strip ->
        UnaryHistory witness ->
          UnaryHistory trivialLedger ->
            UnaryHistory realPart ->
              UnaryHistory rationalLedger ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    UnaryHistory provenance ->
                      UnaryHistory localName ->
                        Cont zero strip stripRead ->
                          Cont stripRead witness witnessRead ->
                            Cont trivialLedger realPart trivialRead ->
                              Cont trivialRead rationalLedger ledgerRead ->
                                Cont witnessRead ledgerRead consumerRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle localName pkg ->
                                      PkgSig bundle consumerRead pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row consumerRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row zero ∨ hsame row strip ∨
                                                hsame row witness ∨
                                                  hsame row trivialLedger ∨
                                                    hsame row realPart ∨
                                                      hsame row rationalLedger ∨
                                                        hsame row witnessRead ∨
                                                          hsame row ledgerRead ∨
                                                            hsame row consumerRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont zero strip stripRead ∧
                                                  Cont stripRead witness witnessRead ∧
                                                    Cont trivialLedger realPart trivialRead ∧
                                                      Cont trivialRead rationalLedger
                                                        ledgerRead ∧
                                                        Cont witnessRead ledgerRead
                                                          consumerRead ∧
                                                          PkgSig bundle consumerRead pkg)
                                            hsame ∧
                                          UnaryHistory stripRead ∧
                                            UnaryHistory witnessRead ∧
                                              UnaryHistory trivialRead ∧
                                                UnaryHistory ledgerRead ∧
                                                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro zeroUnary stripUnary witnessUnary trivialLedgerUnary realPartUnary rationalLedgerUnary
    _transportUnary _replayUnary _provenanceUnary _localNameUnary stripRoute witnessRoute
    trivialRoute ledgerRoute consumerRoute _provenancePkg _localNamePkg consumerPkg
  have stripReadUnary : UnaryHistory stripRead :=
    unary_cont_closed zeroUnary stripUnary stripRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed stripReadUnary witnessUnary witnessRoute
  have trivialReadUnary : UnaryHistory trivialRead :=
    unary_cont_closed trivialLedgerUnary realPartUnary trivialRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed trivialReadUnary rationalLedgerUnary ledgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed witnessReadUnary ledgerReadUnary consumerRoute
  have sourceAtConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead :=
    And.intro (hsame_refl consumerRead) consumerReadUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row zero ∨ hsame row strip ∨ hsame row witness ∨
            hsame row trivialLedger ∨ hsame row realPart ∨ hsame row rationalLedger ∨
              hsame row witnessRead ∨ hsame row ledgerRead ∨ hsame row consumerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont zero strip stripRead ∧ Cont stripRead witness witnessRead ∧
            Cont trivialLedger realPart trivialRead ∧ Cont trivialRead rationalLedger ledgerRead ∧
              Cont witnessRead ledgerRead consumerRead ∧ PkgSig bundle consumerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        And.intro sourceRow.right
          (And.intro stripRoute
            (And.intro witnessRoute
              (And.intro trivialRoute
                (And.intro ledgerRoute
                  (And.intro consumerRoute consumerPkg)))))
  }
  exact
    And.intro cert
      (And.intro stripReadUnary
        (And.intro witnessReadUnary
          (And.intro trivialReadUnary
            (And.intro ledgerReadUnary consumerReadUnary))))

end BEDC.Derived.NontrivialZeroClassifierUp
