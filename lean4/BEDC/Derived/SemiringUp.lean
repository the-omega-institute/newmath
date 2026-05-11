import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SemiringUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SemiringLedger [AskSetup] [PackageSetup]
    (additive multiplicative shared distributive annihilation transport route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory additive ∧ UnaryHistory multiplicative ∧ UnaryHistory shared ∧
    UnaryHistory distributive ∧ UnaryHistory annihilation ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory endpoint ∧ Cont additive multiplicative shared ∧
        Cont shared distributive transport ∧ Cont transport annihilation route ∧
          Cont route transport endpoint ∧ PkgSig bundle endpoint pkg

theorem SemiringLedger_namecert_obligation_surface [AskSetup] [PackageSetup]
    {additive multiplicative shared distributive annihilation transport route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringLedger additive multiplicative shared distributive annihilation transport route
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame := by
  intro ledger
  let Surface : BHist -> Prop :=
    fun row : BHist =>
      SemiringLedger additive multiplicative shared distributive annihilation transport route
        endpoint bundle pkg ∧ hsame row endpoint
  have endpointSource : Surface endpoint :=
    And.intro ledger (hsame_refl endpoint)
  have core : NameCert Surface hsame := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' same
      exact hsame_symm same
    equiv_trans := by
      intro _row _row' _row'' sameRow sameRow'
      exact hsame_trans sameRow sameRow'
    carrier_respects_equiv := by
      intro row row' same sourceRow
      exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
  }
  exact {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.SemiringUp
