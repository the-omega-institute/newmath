import BEDC.Derived.WassersteinUp.TasteGate

namespace BEDC.Derived.WassersteinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WassersteinMetricCouplingScope [AskSetup] [PackageSetup]
    {M K mu nu Gamma A B C H R P N sourceRead couplingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WassersteinTransportPlanCarrier M K mu nu Gamma A B C H R P N bundle pkg →
      Cont M K sourceRead →
        Cont sourceRead Gamma couplingRead →
          SemanticNameCert
              (fun row : BHist => hsame row couplingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row K ∨ hsame row Gamma ∨ hsame row sourceRead ∨
                  hsame row couplingRead)
              (fun row : BHist =>
                hsame row couplingRead ∧ Cont M K sourceRead ∧
                  Cont sourceRead Gamma couplingRead ∧ PkgSig bundle P pkg)
              hsame ∧
            UnaryHistory sourceRead ∧ UnaryHistory couplingRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier sourceRoute couplingRoute
  obtain ⟨mUnary, kUnary, _muUnary, _nuUnary, gammaUnary, _aUnary, _bUnary, _cUnary,
    _hUnary, _rUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed mUnary kUnary sourceRoute
  have couplingUnary : UnaryHistory couplingRead :=
    unary_cont_closed sourceUnary gammaUnary couplingRoute
  have sourceAtCoupling :
      (fun row : BHist => hsame row couplingRead ∧ UnaryHistory row) couplingRead :=
    ⟨hsame_refl couplingRead, couplingUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row couplingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row Gamma ∨ hsame row sourceRead ∨
              hsame row couplingRead)
          (fun row : BHist =>
            hsame row couplingRead ∧ Cont M K sourceRead ∧
              Cont sourceRead Gamma couplingRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro couplingRead sourceAtCoupling
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
      exact ⟨source.left, sourceRoute, couplingRoute, provenancePkg⟩
  }
  exact ⟨cert, sourceUnary, couplingUnary, provenancePkg⟩

end BEDC.Derived.WassersteinUp
