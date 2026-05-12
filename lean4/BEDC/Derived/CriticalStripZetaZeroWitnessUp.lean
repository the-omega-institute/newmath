import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CriticalStripZetaZeroWitnessPacket [AskSetup] [PackageSetup]
    (strip zero line boundary transport route provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory line ∧ UnaryHistory boundary ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ UnaryHistory endpoint ∧ Cont strip zero transport ∧
        Cont line boundary route ∧ Cont transport route endpoint ∧
          Cont endpoint provenance name ∧ hsame endpoint (append transport route) ∧
            PkgSig bundle endpoint pkg

theorem CriticalStripZetaZeroWitnessPacket_namecert_obligations [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance
              name endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
