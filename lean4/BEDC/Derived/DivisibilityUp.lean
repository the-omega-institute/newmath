import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem DivisibilityFiniteHistoryCarrier_mul_witness_transport_closure
    [AskSetup] [PackageSetup]
    {dividend divisor divisor' multiplier multiplier' product product' bound ledger
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
        provenance bundle pkg ->
      hsame divisor divisor' ->
        hsame multiplier multiplier' ->
          Cont divisor' multiplier' product' ->
            DivisibilityFiniteHistoryCarrier dividend divisor' multiplier' product' bound ledger
                provenance bundle pkg ∧ hsame product product' ∧ UnaryHistory product' := by
  intro carrier sameDivisor sameMultiplier productRow'
  obtain ⟨dividendUnary, divisorUnary, multiplierUnary, productUnary, boundUnary, ledgerUnary,
    provenanceUnary, productRow, ledgerRow, provenanceRow, pkgRow⟩ := carrier
  have divisorUnary' : UnaryHistory divisor' :=
    unary_transport divisorUnary sameDivisor
  have multiplierUnary' : UnaryHistory multiplier' :=
    unary_transport multiplierUnary sameMultiplier
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameDivisor sameMultiplier productRow productRow'
  have productUnary' : UnaryHistory product' :=
    unary_transport productUnary sameProduct
  have ledgerRow' : Cont product' bound ledger :=
    cont_hsame_transport sameProduct (hsame_refl bound) (hsame_refl ledger) ledgerRow
  exact
    ⟨⟨dividendUnary, divisorUnary', multiplierUnary', productUnary', boundUnary, ledgerUnary,
        provenanceUnary, productRow', ledgerRow', provenanceRow, pkgRow⟩,
      sameProduct, productUnary'⟩

end BEDC.Derived.DivisibilityUp
