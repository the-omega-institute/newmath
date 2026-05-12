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
  have endpointSource :
      StationaryRationalCauchyCarrier q schedule regseq dyadic «seal» provenance cert endpoint
          bundle pkg ∧ hsame endpoint endpoint :=
    And.intro carrier (hsame_refl endpoint)
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
  exact And.intro carrier.left
    (And.intro carrier.right.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.right.right
          semantic)))

end BEDC.Derived.StationaryRationalCauchyUp
