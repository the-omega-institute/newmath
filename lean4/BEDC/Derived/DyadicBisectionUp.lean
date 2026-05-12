import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicBisectionCarrier [AskSetup] [PackageSetup]
    (initial precision midpoint branch nested endpoint regseq stream real transport route
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory initial ∧ UnaryHistory precision ∧ UnaryHistory midpoint ∧
    UnaryHistory branch ∧ UnaryHistory nested ∧ UnaryHistory endpoint ∧
      UnaryHistory regseq ∧ UnaryHistory stream ∧ UnaryHistory real ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory name ∧
          Cont initial precision midpoint ∧ Cont midpoint branch nested ∧
            Cont nested endpoint regseq ∧ Cont regseq stream real ∧
              Cont real transport route ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg

theorem DyadicBisectionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route
      name : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro real (And.intro carrier (hsame_refl real))
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

end BEDC.Derived.DyadicBisectionUp
