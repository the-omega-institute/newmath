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
    (a b q witness order ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ UnaryHistory order ∧
    Cont b q witness ∧ Cont witness order ledger ∧ Cont ledger provenance provenance ∧
      PkgSig bundle provenance pkg

theorem DivisibilityFiniteHistoryCarrier_mul_witness_closure [AskSetup] [PackageSetup]
    {a b q witness order ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityFiniteHistoryCarrier a b q witness order ledger provenance bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ Cont b q witness ∧
        Cont witness order ledger ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨aUnary, bUnary, qUnary, _orderUnary, witnessRow, ledgerRow, _provenanceRow,
    pkgRow⟩ := carrier
  exact ⟨aUnary, bUnary, qUnary, witnessRow, ledgerRow, pkgRow⟩

end BEDC.Derived.DivisibilityUp
