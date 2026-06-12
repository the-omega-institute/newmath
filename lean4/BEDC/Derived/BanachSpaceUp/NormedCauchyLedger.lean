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

theorem BanachSpaceNormedCauchyLedger [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L cauchyRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg) →
      Cont V N M →
        Cont M Q cauchyRead →
          Cont cauchyRead S completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
                        hsame row cauchyRead ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                        PkgSig bundle P pkg)
                    hsame ∧
                UnaryHistory cauchyRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig UnaryHistory
  intro carrierRows normRoute cauchyRoute completionRoute completionPkg
  have unaryV : UnaryHistory V := carrierRows.left
  have unaryN : UnaryHistory N := carrierRows.right.left
  have unaryM : UnaryHistory M := carrierRows.right.right.left
  have unaryQ : UnaryHistory Q := carrierRows.right.right.right.left
  have pkgP : PkgSig bundle P pkg :=
    carrierRows.right.right.right.right.right.right.right.right.right.right.right.right
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unaryM unaryQ cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary carrierRows.right.right.right.right.left completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
              hsame row cauchyRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionPkg, pkgP⟩
  }
  exact ⟨cert, cauchyUnary, completionUnary⟩

end BEDC.Derived.BanachSpaceUp
