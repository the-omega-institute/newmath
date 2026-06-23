import BEDC.Derived.WassersteinUp.TasteGate

namespace BEDC.Derived.WassersteinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WassersteinRealCostReadbackScope [AskSetup] [PackageSetup]
    {M K mu nu Gamma A B C H R P N metricRead costRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WassersteinTransportPlanCarrier M K mu nu Gamma A B C H R P N bundle pkg →
      Cont M Gamma metricRead →
        Cont metricRead C costRead →
          SemanticNameCert
              (fun row : BHist => hsame row costRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row Gamma ∨ hsame row C ∨ hsame row metricRead ∨
                  hsame row costRead)
              (fun row : BHist =>
                hsame row costRead ∧ Cont M Gamma metricRead ∧
                  Cont metricRead C costRead ∧ PkgSig bundle P pkg)
              hsame ∧
            UnaryHistory metricRead ∧ UnaryHistory costRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier metricRoute costRoute
  obtain ⟨mUnary, _kUnary, _muUnary, _nuUnary, gammaUnary, _aUnary, _bUnary, cUnary,
    _hUnary, _rUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed mUnary gammaUnary metricRoute
  have costUnary : UnaryHistory costRead :=
    unary_cont_closed metricUnary cUnary costRoute
  have sourceAtCost :
      (fun row : BHist => hsame row costRead ∧ UnaryHistory row) costRead :=
    ⟨hsame_refl costRead, costUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row costRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Gamma ∨ hsame row C ∨ hsame row metricRead ∨
              hsame row costRead)
          (fun row : BHist =>
            hsame row costRead ∧ Cont M Gamma metricRead ∧
              Cont metricRead C costRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro costRead sourceAtCost
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, metricRoute, costRoute, provenancePkg⟩
  }
  exact ⟨cert, metricUnary, costUnary, provenancePkg⟩

end BEDC.Derived.WassersteinUp
