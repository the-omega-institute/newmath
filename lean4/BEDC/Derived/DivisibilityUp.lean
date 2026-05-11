import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DivisibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DivisibilityFiniteHistoryCarrier [AskSetup] [PackageSetup]
    (dividend divisor multiplier product bound ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dividend ∧ UnaryHistory divisor ∧ UnaryHistory multiplier ∧
    UnaryHistory product ∧ UnaryHistory bound ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont divisor multiplier product ∧
        Cont product bound ledger ∧ Cont ledger provenance provenance ∧
          PkgSig bundle provenance pkg

theorem DivisibilityFiniteHistoryCarrier_order_bounded_ledger
    [AskSetup] [PackageSetup]
    {dividend divisor multiplier product bound ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
        provenance bundle pkg ->
      UnaryHistory bound ∧ UnaryHistory ledger ∧ hsame ledger (append product bound) ∧
        hsame provenance (append ledger provenance) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_dividendUnary, _divisorUnary, _multiplierUnary, _productUnary, boundUnary,
    ledgerUnary, _provenanceUnary, _productRow, ledgerRow, provenanceRow, pkgRow⟩ := carrier
  exact ⟨boundUnary, ledgerUnary, ledgerRow, provenanceRow, pkgRow⟩

theorem DivisibilityFiniteHistoryCarrier_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {dividend divisor multiplier product bound ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
        provenance bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          hsame ∧
        UnaryHistory dividend ∧ UnaryHistory divisor ∧ UnaryHistory multiplier ∧
          UnaryHistory product ∧ UnaryHistory bound ∧ UnaryHistory ledger ∧
            UnaryHistory provenance ∧ hsame product (append divisor multiplier) ∧
              hsame ledger (append product bound) ∧
                hsame provenance (append ledger provenance) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row provenance)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  obtain ⟨dividendUnary, divisorUnary, multiplierUnary, productUnary, boundUnary,
    ledgerUnary, provenanceUnary, productRow, ledgerRow, provenanceRow, pkgRow⟩ := carrier
  exact
    ⟨cert, dividendUnary, divisorUnary, multiplierUnary, productUnary, boundUnary,
      ledgerUnary, provenanceUnary, productRow, ledgerRow, provenanceRow, pkgRow⟩

end BEDC.Derived.DivisibilityUp
