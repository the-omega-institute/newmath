import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICNormalizationBudgetCarrier [AskSetup] [PackageSetup]
    (T C E S A P R H Q L N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory S ∧
    UnaryHistory A ∧ UnaryHistory P ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory Q ∧ UnaryHistory L ∧ UnaryHistory N ∧ Cont T C E ∧
        Cont E S A ∧ Cont A P R ∧ Cont R H Q ∧ PkgSig bundle L pkg ∧
          PkgSig bundle N pkg

theorem MetaCICNormalizationBudgetCarrier_candidate_budget_namecert [AskSetup]
    [PackageSetup]
    {T C E S A P R H Q L N positiveRead adequacyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationBudgetCarrier T C E S A P R H Q L N bundle pkg →
      Cont E S positiveRead →
        Cont positiveRead A adequacyRead →
          PkgSig bundle adequacyRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row adequacyRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row adequacyRead)
              (fun row : BHist => hsame row adequacyRead ∧ PkgSig bundle adequacyRead pkg)
              hsame ∧ UnaryHistory positiveRead ∧ UnaryHistory adequacyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier positiveRoute adequacyRoute adequacyPkg
  obtain ⟨_unaryT, _unaryC, unaryE, unaryS, unaryA, _unaryP, _unaryR, _unaryH,
    _unaryQ, _unaryL, _unaryN, _routeTC, _routeES, _routeAP, _routeRH, _pkgL,
    _pkgN⟩ := carrier
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed unaryE unaryS positiveRoute
  have adequacyUnary : UnaryHistory adequacyRead :=
    unary_cont_closed positiveUnary unaryA adequacyRoute
  have sourceAdequacy :
      (fun row : BHist => hsame row adequacyRead ∧ UnaryHistory row) adequacyRead := by
    exact ⟨hsame_refl adequacyRead, adequacyUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row adequacyRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row adequacyRead)
        (fun row : BHist => hsame row adequacyRead ∧ PkgSig bundle adequacyRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro adequacyRead sourceAdequacy
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, adequacyPkg⟩
  }
  exact ⟨cert, positiveUnary, adequacyUnary⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
