import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorCarrier_route_rows [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N requestRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W requestRead →
        PkgSig bundle P pkg →
          SemanticNameCert
              (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                  hsame row A ∨ hsame row requestRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont epsilon W requestRead ∧ PkgSig bundle P pkg)
              hsame ∧
            UnaryHistory requestRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier requestRoute packageProof
  obtain ⟨epsilonUnary, windowUnary, _rUnary, _dUnary, _aUnary, _sigmaUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed epsilonUnary windowUnary requestRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row requestRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilon W requestRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro requestRead ⟨hsame_refl requestRead, requestUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, requestRoute, packageProof⟩
  }
  exact ⟨cert, requestUnary⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
