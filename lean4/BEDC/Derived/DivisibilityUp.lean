import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.PrimeUp

namespace BEDC.Derived.DivisibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp

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

def DivisibilityLedger [AskSetup] [PackageSetup]
    (a b q w order ledger provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ NatMul b q a ∧ Cont b q w ∧
    Cont q order ledger ∧ Cont ledger provenance provenance ∧ PkgSig bundle provenance pkg

theorem DivisibilityLedger_mul_witness_closure [AskSetup] [PackageSetup]
    {a b q w order ledger provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityLedger a b q w order ledger provenance bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ NatMul b q a ∧ Cont b q w ∧
        PkgSig bundle provenance pkg := by
  intro source
  exact
    And.intro source.left
      (And.intro source.right.left
        (And.intro source.right.right.left
          (And.intro source.right.right.right.left
            (And.intro source.right.right.right.right.left
              source.right.right.right.right.right.right.right))))

end BEDC.Derived.DivisibilityUp
