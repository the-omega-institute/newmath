import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DivisibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

def DivisibilityLedgerCarrier [AskSetup] [PackageSetup]
    (a b q w o ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ UnaryHistory o ∧
    UnaryHistory provenance ∧ Cont b q w ∧ Cont w o ledger ∧
      Cont ledger provenance provenance ∧ PkgSig bundle provenance pkg

theorem DivisibilityLedgerCarrier_mul_witness_closure [AskSetup] [PackageSetup]
    {a b q w o ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityLedgerCarrier a b q w o ledger provenance bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ UnaryHistory w ∧
        hsame w (append b q) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have unaryA : UnaryHistory a :=
    carrier.left
  have unaryB : UnaryHistory b :=
    carrier.right.left
  have unaryQ : UnaryHistory q :=
    carrier.right.right.left
  have contWitness : Cont b q w :=
    carrier.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right
  have unaryW : UnaryHistory w :=
    unary_cont_closed unaryB unaryQ contWitness
  have witnessRead : hsame w (append b q) :=
    contWitness
  exact And.intro unaryA
    (And.intro unaryB
      (And.intro unaryQ
        (And.intro unaryW
          (And.intro witnessRead pkgSig))))

end BEDC.Derived.DivisibilityUp
