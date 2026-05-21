import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# FiniteErrorBudgetUp finite carrier and semantic NameCert surface.
-/

namespace BEDC.Derived.FiniteErrorBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

/-- Finite carrier surface for precision-budget readback into a real seal. -/
def FiniteErrorBudgetCarrier [AskSetup] [PackageSetup]
    (requestRow toleranceRow selectorRow tailRow budgetRow readbackRow sealRow provenanceRow
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory requestRow ∧ UnaryHistory toleranceRow ∧ UnaryHistory selectorRow ∧
    UnaryHistory tailRow ∧ UnaryHistory budgetRow ∧ UnaryHistory readbackRow ∧
      UnaryHistory sealRow ∧ UnaryHistory provenanceRow ∧ UnaryHistory nameRow ∧
        Cont requestRow toleranceRow selectorRow ∧ Cont selectorRow tailRow budgetRow ∧
          Cont budgetRow readbackRow sealRow ∧ hsame provenanceRow (append sealRow nameRow) ∧
            PkgSig bundle provenanceRow pkg

theorem FiniteErrorBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {requestRow toleranceRow selectorRow tailRow budgetRow readbackRow sealRow provenanceRow
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
        readbackRow sealRow provenanceRow nameRow bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
            readbackRow sealRow provenanceRow nameRow bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
            readbackRow sealRow provenanceRow nameRow bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
            readbackRow sealRow provenanceRow nameRow bundle pkg ∧ hsame row sealRow)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier rfl)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same source
        cases source with
        | intro carrierData sourceSame =>
            cases same
            exact And.intro carrierData sourceSame
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }

theorem FiniteErrorBudgetCarrier_diagonal_selector_exactness [AskSetup] [PackageSetup]
    {requestRow toleranceRow selectorRow tailRow budgetRow readbackRow sealRow provenanceRow
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
        readbackRow sealRow provenanceRow nameRow bundle pkg →
      Cont requestRow toleranceRow selectorRow ∧ Cont selectorRow tailRow budgetRow ∧
        Cont budgetRow readbackRow sealRow ∧ UnaryHistory selectorRow ∧
          UnaryHistory tailRow ∧ UnaryHistory budgetRow ∧ UnaryHistory readbackRow ∧
            UnaryHistory sealRow := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier
  cases carrier with
  | intro _requestUnary carrier =>
      cases carrier with
      | intro _toleranceUnary carrier =>
          cases carrier with
          | intro selectorUnary carrier =>
              cases carrier with
              | intro tailUnary carrier =>
                  cases carrier with
                  | intro budgetUnary carrier =>
                      cases carrier with
                      | intro readbackUnary carrier =>
                          cases carrier with
                          | intro sealUnary carrier =>
                              cases carrier with
                              | intro _provenanceUnary carrier =>
                                  cases carrier with
                                  | intro _nameUnary carrier =>
                                      cases carrier with
                                      | intro requestToSelector carrier =>
                                          cases carrier with
                                          | intro selectorToBudget carrier =>
                                              cases carrier with
                                              | intro budgetToSeal _carrier =>
                                                  exact
                                                    ⟨requestToSelector, selectorToBudget,
                                                      budgetToSeal, selectorUnary, tailUnary,
                                                      budgetUnary, readbackUnary, sealUnary⟩

theorem FiniteErrorBudgetCarrier_completion_consumer_boundary [AskSetup] [PackageSetup]
    {requestRow toleranceRow selectorRow tailRow budgetRow readbackRow sealRow provenanceRow
      nameRow consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow
        readbackRow sealRow provenanceRow nameRow bundle pkg →
      Cont sealRow provenanceRow consumerRead →
        UnaryHistory consumerRead ∧ hsame provenanceRow (append sealRow nameRow) ∧
          PkgSig bundle provenanceRow pkg ∧ Cont sealRow provenanceRow consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier sealToConsumer
  cases carrier with
  | intro _requestUnary carrier =>
      cases carrier with
      | intro _toleranceUnary carrier =>
          cases carrier with
          | intro _selectorUnary carrier =>
              cases carrier with
              | intro _tailUnary carrier =>
                  cases carrier with
                  | intro _budgetUnary carrier =>
                      cases carrier with
                      | intro _readbackUnary carrier =>
                          cases carrier with
                          | intro sealUnary carrier =>
                              cases carrier with
                              | intro provenanceUnary carrier =>
                                  cases carrier with
                                  | intro _nameUnary carrier =>
                                      cases carrier with
                                      | intro _requestToSelector carrier =>
                                          cases carrier with
                                          | intro _selectorToBudget carrier =>
                                              cases carrier with
                                              | intro _budgetToSeal carrier =>
                                                  cases carrier with
                                                  | intro provenanceName pkgSig =>
                                                      exact
                                                        ⟨unary_repetition_closed_under_continuation
                                                            sealUnary provenanceUnary
                                                            sealToConsumer,
                                                          provenanceName, pkgSig,
                                                          sealToConsumer⟩

end BEDC.Derived.FiniteErrorBudgetUp
