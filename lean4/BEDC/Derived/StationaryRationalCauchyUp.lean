import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryRationalCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryRationalCauchyCarrier [AskSetup] [PackageSetup]
    (q schedule regseq dyadic «seal» provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
    UnaryHistory «seal» ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      Cont q schedule regseq ∧ Cont regseq dyadic «seal» ∧ Cont provenance cert endpoint ∧
        PkgSig bundle endpoint pkg

theorem StationaryRationalCauchyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q schedule regseq dyadic «seal» provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
        bundle pkg ->
      UnaryHistory q ∧ Cont q schedule regseq ∧ Cont regseq dyadic «seal» ∧
        PkgSig bundle endpoint pkg ∧
          SemanticNameCert
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            (fun row : BHist =>
              StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert
                endpoint bundle pkg ∧ hsame row endpoint)
            hsame := by
  intro carrier
  have carrierCopy :
      StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
          bundle pkg :=
    carrier
  obtain ⟨qUnary, _scheduleUnary, _regseqUnary, _dyadicUnary, _sealUnary, _provenanceUnary,
    _certUnary, regseqRow, sealRow, _endpointRow, pkgRow⟩ := carrier
  have endpointSource :
      StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
          bundle pkg ∧ hsame endpoint endpoint :=
    And.intro carrierCopy (hsame_refl endpoint)
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
            bundle pkg ∧ hsame row endpoint)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro qUnary
    (And.intro regseqRow (And.intro sealRow (And.intro pkgRow semantic)))

theorem StationaryRationalCauchyCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {q schedule regseq dyadic «seal» provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
        bundle pkg →
      UnaryHistory q ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧
        UnaryHistory dyadic ∧ UnaryHistory «seal» ∧
          hsame regseq (append q schedule) ∧
            hsame «seal» (append regseq dyadic) ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨qUnary, scheduleUnary, regseqUnary, dyadicUnary, sealUnary, _provenanceUnary,
    _certUnary, regseqRow, sealRow, _endpointRow, pkgRow⟩ := carrier
  exact
    And.intro qUnary
      (And.intro scheduleUnary
        (And.intro regseqUnary
          (And.intro dyadicUnary
            (And.intro sealUnary
              (And.intro regseqRow
                (And.intro sealRow pkgRow))))))

end BEDC.Derived.StationaryRationalCauchyUp
