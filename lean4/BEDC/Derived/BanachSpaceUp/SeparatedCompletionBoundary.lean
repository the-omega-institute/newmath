import BEDC.Derived.BanachSpaceUp.CauchyWindowScope
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceSeparatedCompletionBoundary [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L completionRead separatedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg ∧ PkgSig bundle L pkg) →
      Cont S Z separatedRead →
        Cont separatedRead L namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row separatedRead ∨ hsame row namedRead ∨
                      hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle namedRead pkg ∧
                      PkgSig bundle P pkg)
                  hsame ∧
              UnaryHistory separatedRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig UnaryHistory
  intro carrierRows separatedRoute namedRoute namedPkg
  have unaryS : UnaryHistory S := carrierRows.right.right.right.right.left
  have unaryZ : UnaryHistory Z :=
    carrierRows.right.right.right.right.right.right.right.left
  have unaryL : UnaryHistory L :=
    carrierRows.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgP : PkgSig bundle P pkg :=
    carrierRows.right.right.right.right.right.right.right.right.right.right.right.right.left
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed unaryS unaryZ separatedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separatedUnary unaryL namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row separatedRead ∨ hsame row namedRead ∨
              hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle namedRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namedPkg, pkgP⟩
  }
  exact ⟨cert, separatedUnary, namedUnary⟩

end BEDC.Derived.BanachSpaceUp
