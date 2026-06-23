import BEDC.Derived.LocatedWeakKonigUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedWeakKonigUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedWeakKonigCarrier [AskSetup] [PackageSetup]
    (T B W E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle N pkg

theorem LocatedWeakKonig_namecert_obligations [AskSetup] [PackageSetup]
    {T B W E H C P N auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedWeakKonigCarrier T B W E H C P N bundle pkg ->
      Cont E H auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row T ∨ hsame row B ∨ hsame row W ∨ hsame row E ∨
                  hsame row auditRead)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory T ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory E ∧
              UnaryHistory auditRead ∧ Cont E H auditRead ∧ PkgSig bundle N pkg ∧
                PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditRoute auditPkg
  obtain ⟨tUnary, bUnary, wUnary, eUnary, hUnary, _cUnary, _pUnary, _nUnary,
    namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed eUnary hUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row B ∨ hsame row W ∨ hsame row E ∨
              hsame row auditRead)
          (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, tUnary, bUnary, wUnary, eUnary, auditUnary, auditRoute, namePkg, auditPkg⟩

end BEDC.Derived.LocatedWeakKonigUp
