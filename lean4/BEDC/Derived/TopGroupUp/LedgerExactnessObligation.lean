import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_ledger_exactness_obligation
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      continuityLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger continuityLedger ->
            SemanticNameCert (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance) hsame ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
              UnaryHistory continuityLedger ∧
                hsame continuityLedger (append productLedger inverseLedger) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productCont inverseCont continuityCont
  have cert := TopGroupRootThresholdPackage_export_boundary_certificate package
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseCont
  have continuityLedgerUnary : UnaryHistory continuityLedger :=
    unary_cont_closed productLedgerUnary inverseLedgerUnary continuityCont
  exact And.intro cert.left
    (And.intro productLedgerUnary
      (And.intro inverseLedgerUnary
        (And.intro continuityLedgerUnary
          (And.intro continuityCont
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
