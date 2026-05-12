import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryPartitionDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryPartitionDiagonalCarrier [AskSetup] [PackageSetup]
    (rat partition diagonal constantStream dyadic realSeal ledger transport provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory rat ∧ UnaryHistory partition ∧ UnaryHistory diagonal ∧
    UnaryHistory constantStream ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
      UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ UnaryHistory endpoint ∧
          Cont rat partition diagonal ∧ Cont diagonal constantStream dyadic ∧
            Cont dyadic realSeal ledger ∧ Cont ledger transport provenance ∧
              Cont provenance localCert endpoint ∧ hsame endpoint (append provenance localCert) ∧
                PkgSig bundle endpoint pkg

theorem StationaryPartitionDiagonalCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {rat partition diagonal constantStream dyadic realSeal ledger transport provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryPartitionDiagonalCarrier rat partition diagonal constantStream dyadic realSeal ledger
        transport provenance localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StationaryPartitionDiagonalCarrier rat partition diagonal constantStream dyadic realSeal
            ledger transport provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryPartitionDiagonalCarrier rat partition diagonal constantStream dyadic realSeal
            ledger transport provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryPartitionDiagonalCarrier rat partition diagonal constantStream dyadic realSeal
            ledger transport provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
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
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.StationaryPartitionDiagonalUp
