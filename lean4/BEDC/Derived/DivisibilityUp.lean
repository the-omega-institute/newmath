import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.PrimeUp.DividesClosure

namespace BEDC.Derived.DivisibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def DivisibilityLedger [AskSetup] [PackageSetup]
    (a b q witness order ledger provenance product : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ UnaryHistory witness ∧
    UnaryHistory order ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      Cont b q product ∧ hsame product a ∧ Cont witness ledger product ∧
        PkgSig bundle provenance pkg

theorem DivisibilityLedger_multiplication_witness_closure [AskSetup] [PackageSetup]
    {a b q witness order ledger provenance product : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityLedger a b q witness order ledger provenance product bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory q ∧ Cont b q product ∧
        hsame product a ∧ Cont witness ledger product ∧ PkgSig bundle provenance pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right.right.right.right)))))

theorem DivisibilityFiniteHistoryCarrier_public_certificate_export
    [AskSetup] [PackageSetup]
    {dividend divisor multiplier product bound ledger provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
        provenance bundle pkg ->
      Cont provenance product consumer ->
        SemanticNameCert
            (fun row : BHist =>
              DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
                provenance bundle pkg ∧ hsame row consumer)
            (fun row : BHist =>
              DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
                provenance bundle pkg ∧ hsame row consumer)
            (fun row : BHist =>
              DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
                provenance bundle pkg ∧ hsame row consumer)
            hsame ∧
          UnaryHistory dividend ∧ UnaryHistory divisor ∧ UnaryHistory multiplier ∧
            UnaryHistory product ∧ UnaryHistory bound ∧ UnaryHistory ledger ∧
              UnaryHistory provenance ∧ UnaryHistory consumer ∧ Cont divisor multiplier product ∧
                Cont product bound ledger ∧ Cont ledger provenance provenance ∧
                  Cont provenance product consumer ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRow
  obtain ⟨dividendUnary, divisorUnary, multiplierUnary, productUnary, boundUnary,
    ledgerUnary, provenanceUnary, productRow, ledgerRow, provenanceRow, pkgRow⟩ := carrier
  have sourceCarrier :
      DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger provenance
        bundle pkg :=
    And.intro dividendUnary
      (And.intro divisorUnary
        (And.intro multiplierUnary
          (And.intro productUnary
            (And.intro boundUnary
              (And.intro ledgerUnary
                (And.intro provenanceUnary
                  (And.intro productRow
                    (And.intro ledgerRow
                      (And.intro provenanceRow pkgRow)))))))))
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary productUnary consumerRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row consumer)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row consumer)
          (fun row : BHist =>
            DivisibilityFiniteHistoryCarrier dividend divisor multiplier product bound ledger
              provenance bundle pkg ∧ hsame row consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer (And.intro sourceCarrier (hsame_refl consumer))
      equiv_refl := by
        intro row _carrierRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact And.intro carrierRow.left
          (hsame_trans (hsame_symm sameRows) carrierRow.right)
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }
  exact And.intro cert
    (And.intro dividendUnary
      (And.intro divisorUnary
        (And.intro multiplierUnary
          (And.intro productUnary
            (And.intro boundUnary
              (And.intro ledgerUnary
                (And.intro provenanceUnary
                  (And.intro consumerUnary
                    (And.intro productRow
                      (And.intro ledgerRow
                        (And.intro provenanceRow
                          (And.intro consumerRow pkgRow))))))))))))

end BEDC.Derived.DivisibilityUp
