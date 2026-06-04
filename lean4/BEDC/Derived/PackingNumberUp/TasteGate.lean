import BEDC.Derived.PackingNumberUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PackingNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PackingNumberNamecertObligations [AskSetup] [PackageSetup]
    {X eps U D B H C P N separatedRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackingNumberCarrier X eps U D B H C P N separatedRead bundle pkg ->
      Cont separatedRead D budgetRead ->
        PkgSig bundle budgetRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨
                  hsame row B ∨ hsame row separatedRead ∨ hsame row budgetRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X U separatedRead ∧
                  Cont separatedRead D budgetRead ∧ PkgSig bundle budgetRead pkg)
              hsame ∧
            UnaryHistory X ∧ UnaryHistory eps ∧ UnaryHistory U ∧ UnaryHistory D ∧
              UnaryHistory B ∧ UnaryHistory separatedRead ∧ UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedBudget budgetPkg
  obtain ⟨xUnary, epsUnary, uUnary, dUnary, bUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, separatedUnary, sourceCentersSeparated, _provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed separatedUnary dUnary separatedBudget
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row eps ∨ hsame row U ∨ hsame row D ∨
              hsame row B ∨ hsame row separatedRead ∨ hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X U separatedRead ∧ Cont separatedRead D budgetRead ∧
              PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceCentersSeparated, separatedBudget, budgetPkg⟩
  }
  exact
    ⟨cert, xUnary, epsUnary, uUnary, dUnary, bUnary, separatedUnary, budgetUnary⟩

end BEDC.Derived.PackingNumberUp
