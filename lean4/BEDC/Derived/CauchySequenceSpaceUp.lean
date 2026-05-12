import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySequenceSpaceCarrier [AskSetup] [PackageSetup]
    (family schedule window tolerance completion transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
    UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory name ∧ Cont family schedule window ∧
        Cont window tolerance completion ∧ Cont completion transport route ∧
          PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem CauchySequenceSpaceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {family schedule window tolerance completion transport route name : BHist} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro completion (And.intro carrier (hsame_refl completion))
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

end BEDC.Derived.CauchySequenceSpaceUp
