import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCompletionSelectorSealCarrier [AskSetup] [PackageSetup]
    (b w r l e h c p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  UnaryHistory b ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory l ∧
    UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
      UnaryHistory n ∧ Cont b w r ∧ Cont r l e ∧ PkgSig bundle p pkg ∧ hsame h n

theorem RealCompletionSelectorSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {b w r l e h c p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ∧ hsame row e)
        (fun row : BHist =>
          Cont b w r ∧ Cont r l e ∧ hsame row e ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  have bUnary : UnaryHistory b := carrier.left
  have wUnary : UnaryHistory w := carrier.right.left
  have rUnary : UnaryHistory r := carrier.right.right.left
  have lUnary : UnaryHistory l := carrier.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.left
  have hUnary : UnaryHistory h := carrier.right.right.right.right.right.left
  have cUnary : UnaryHistory c := carrier.right.right.right.right.right.right.left
  have pUnary : UnaryHistory p := carrier.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory n := carrier.right.right.right.right.right.right.right.right.left
  have bwr : Cont b w r := carrier.right.right.right.right.right.right.right.right.right.left
  have rle : Cont r l e := carrier.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have hn : hsame h n :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro e (And.intro
          ⟨bUnary, wUnary, rUnary, lUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
            bwr, rle, pPkg, hn⟩
          (hsame_refl e))
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
      intro row source
      exact ⟨bwr, rle, source.right, pPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport eUnary (hsame_symm source.right)) pPkg
  }

end BEDC.Derived.RealCompletionSelectorSealUp
