import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.PrimeUp.DividesClosure

namespace BEDC.Derived.DivisibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp

def DivisibilityBHistCarrier [AskSetup] [PackageSetup]
    (dividend divisor multiplier productWitness bound ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dividend ∧
    UnaryHistory divisor ∧
      UnaryHistory multiplier ∧
        NatMul divisor multiplier dividend ∧
          Cont divisor multiplier productWitness ∧
            Cont multiplier dividend bound ∧
              Cont productWitness bound ledger ∧
                Cont ledger provenance provenance ∧
                  PkgSig bundle provenance pkg

theorem DivisibilityBHistCarrier_mul_witness_closure [AskSetup] [PackageSetup]
    {dividend divisor multiplier productWitness bound ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityBHistCarrier dividend divisor multiplier productWitness bound ledger provenance
        bundle pkg ->
      NatDivides divisor dividend ∧ UnaryHistory productWitness ∧
        Cont divisor multiplier productWitness ∧ PkgSig bundle provenance pkg := by
  intro carrier
  cases carrier with
  | intro dividendUnary rest =>
      cases rest with
      | intro divisorUnary rest =>
          cases rest with
          | intro multiplierUnary rest =>
              cases rest with
              | intro mul rest =>
                  cases rest with
                  | intro productRow rest =>
                      cases rest with
                      | intro _boundRow rest =>
                          cases rest with
                          | intro _ledgerRow rest =>
                              cases rest with
                              | intro _provenanceRow pkgSig =>
                                  exact
                                    ⟨Exists.intro multiplier (And.intro multiplierUnary mul),
                                      unary_cont_closed divisorUnary multiplierUnary productRow,
                                      productRow,
                                      pkgSig⟩

theorem DivisibilityBHistCarrier_order_bounded_ledger [AskSetup] [PackageSetup]
    {dividend divisor multiplier productWitness bound ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityBHistCarrier dividend divisor multiplier productWitness bound ledger provenance
        bundle pkg ->
      UnaryHistory bound ∧ Cont multiplier dividend bound ∧
        hsame bound (append multiplier dividend) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  cases carrier with
  | intro _dividendUnary rest =>
      cases rest with
      | intro divisorUnary rest =>
          cases rest with
          | intro multiplierUnary rest =>
              cases rest with
              | intro mul rest =>
                  cases rest with
                  | intro _productRow rest =>
                      cases rest with
                      | intro boundRow rest =>
                          cases rest with
                          | intro _ledgerRow rest =>
                              cases rest with
                              | intro _provenanceRow pkgSig =>
                                  have dividendUnary : UnaryHistory dividend :=
                                    NatMul_result_unary divisorUnary mul
                                  exact
                                    ⟨unary_cont_closed multiplierUnary dividendUnary boundRow,
                                      boundRow,
                                      boundRow,
                                      pkgSig⟩

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

theorem DivisibilityMulWitness_closure [AskSetup] [PackageSetup]
    {dividend divisor multiplier productWitness provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dividend -> UnaryHistory divisor -> UnaryHistory multiplier ->
      Cont divisor multiplier productWitness -> PkgSig bundle provenance pkg ->
        UnaryHistory dividend ∧ UnaryHistory divisor ∧ UnaryHistory multiplier ∧
          UnaryHistory productWitness ∧ hsame productWitness (append divisor multiplier) ∧
            PkgSig bundle provenance pkg := by
  intro dividendUnary divisorUnary multiplierUnary productRow pkgRow
  have productUnary : UnaryHistory productWitness :=
    unary_cont_closed divisorUnary multiplierUnary productRow
  exact
    ⟨dividendUnary, divisorUnary, multiplierUnary, productUnary, productRow, pkgRow⟩

end BEDC.Derived.DivisibilityUp
