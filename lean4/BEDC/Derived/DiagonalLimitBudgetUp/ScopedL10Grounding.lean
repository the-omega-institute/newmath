import BEDC.Derived.DiagonalLimitBudgetUp.CarrierAdmission
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitBudgetScopedL10Grounding [AskSetup] [PackageSetup]
    {D M W Q E H C P N streamRead dyadicRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitBudgetCarrier D M W Q E H C P N bundle pkg →
      Cont D M streamRead →
        Cont streamRead W dyadicRead →
          Cont dyadicRead Q realRead →
            Cont realRead N namedRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row M ∨ hsame row W ∨
                          hsame row Q ∨ hsame row E ∨ hsame row namedRead)
                      (fun row : BHist =>
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row namedRead)
                      hsame ∧
                    UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier streamRoute dyadicRoute realRoute namedRoute pPkg nPkg
  obtain ⟨dUnary, mUnary, wUnary, qUnary, _eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _windowRoute, _dyadicRoute, _provenancePkg, _namePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dUnary mUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary wUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary qUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact ⟨pPkg, nPkg, source.left⟩
  }
  exact ⟨cert, streamUnary, dyadicUnary, realUnary, namedUnary⟩

end BEDC.Derived.DiagonalLimitBudgetUp
