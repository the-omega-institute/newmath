import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Derived.GapClosureBoundaryUp.TasteGate

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem GapClosureBoundary_namecert_obligations [AskSetup] [PackageSetup]
    {G S R H C P N sourceRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont G S sourceRead ->
      Cont G C refusalRead ->
        PkgSig bundle sourceRead pkg ->
          PkgSig bundle refusalRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                (hsame row sourceRead ∨ hsame row refusalRead) ∧
                  ∃ packet : GapClosureBoundaryUp,
                    packet = GapClosureBoundaryUp.mk G S R H C P N)
              (fun row : BHist =>
                (Cont G S sourceRead ∧ hsame row sourceRead) ∨
                  (Cont G C refusalRead ∧ hsame row refusalRead))
              (fun row : BHist =>
                (hsame row sourceRead ∧ PkgSig bundle sourceRead pkg) ∨
                  (hsame row refusalRead ∧ PkgSig bundle refusalRead pkg))
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro sourceRoute refusalRoute sourcePkg refusalPkg
  exact {
    core := {
      carrier_inhabited := by
        exact Exists.intro sourceRead
          (And.intro (Or.inl (hsame_refl sourceRead))
            (Exists.intro (GapClosureBoundaryUp.mk G S R H C P N) rfl))
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
        cases source with
        | intro branch packet =>
          cases branch with
          | inl sourceSame =>
              exact And.intro
                (Or.inl (hsame_trans (hsame_symm sameRows) sourceSame)) packet
          | inr refusalSame =>
              exact And.intro
                (Or.inr (hsame_trans (hsame_symm sameRows) refusalSame)) packet
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sourceSame =>
          exact Or.inl (And.intro sourceRoute sourceSame)
      | inr refusalSame =>
          exact Or.inr (And.intro refusalRoute refusalSame)
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sourceSame =>
          exact Or.inl (And.intro sourceSame sourcePkg)
      | inr refusalSame =>
          exact Or.inr (And.intro refusalSame refusalPkg)
  }

end BEDC.Derived.GapClosureBoundaryUp
