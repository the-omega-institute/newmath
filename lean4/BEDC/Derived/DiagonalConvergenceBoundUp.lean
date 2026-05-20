import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalConvergenceBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalConvergenceBoundCarrier [AskSetup] [PackageSetup]
    (X mu n D Q R E H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory mu ∧ UnaryHistory n ∧ UnaryHistory D ∧
    UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont mu n D ∧ Cont D Q R ∧ Cont R E endpoint ∧ Cont H C P ∧
          Cont P N endpoint ∧ PkgSig bundle endpoint pkg

theorem DiagonalConvergenceBoundNameCertObligations [AskSetup] [PackageSetup]
    {X mu n D Q R E H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalConvergenceBoundCarrier X mu n D Q R E H C P N endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          DiagonalConvergenceBoundCarrier X mu n D Q R E H C P N endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DiagonalConvergenceBoundCarrier X mu n D Q R E H C P N endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DiagonalConvergenceBoundCarrier X mu n D Q R E H C P N endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.DiagonalConvergenceBoundUp
