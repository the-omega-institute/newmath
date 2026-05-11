import BEDC.FKernel.Package
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

end BEDC.Derived.DivisibilityUp
