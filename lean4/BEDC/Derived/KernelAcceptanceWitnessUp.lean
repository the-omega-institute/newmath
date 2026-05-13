import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KernelAcceptanceWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KernelAcceptanceWitnessPacket [AskSetup] [PackageSetup]
    (generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generated ∧ UnaryHistory accepted ∧ UnaryHistory environmentLedger ∧
    UnaryHistory axiomQuery ∧ UnaryHistory refusal ∧ UnaryHistory nameCert ∧
      Cont generated environmentLedger accepted ∧ Cont accepted axiomQuery transport ∧
        Cont transport refusal routes ∧ Cont routes nameCert provenance ∧
          Cont provenance accepted acceptance ∧ PkgSig bundle acceptance pkg

theorem KernelAcceptanceWitnessPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
        transport routes provenance nameCert acceptance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.KernelAcceptanceWitnessUp
