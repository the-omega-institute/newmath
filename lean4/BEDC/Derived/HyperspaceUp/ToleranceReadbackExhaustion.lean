import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem HyperspaceToleranceReadbackExhaustion [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M readbackLeft readbackRight symmetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 R readbackLeft ->
        Cont D1 R readbackRight ->
          Cont readbackLeft readbackRight symmetricRead ->
            PkgSig bundle symmetricRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row symmetricRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                      hsame row readbackLeft ∨ hsame row readbackRight ∨
                        hsame row symmetricRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle symmetricRead pkg)
                  hsame ∧
                UnaryHistory readbackLeft ∧ UnaryHistory readbackRight ∧
                  UnaryHistory symmetricRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier leftRoute rightRoute symmetricRoute symmetricPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory readbackLeft :=
    unary_cont_closed d0Unary rUnary leftRoute
  have rightUnary : UnaryHistory readbackRight :=
    unary_cont_closed d1Unary rUnary rightRoute
  have symmetricUnary : UnaryHistory symmetricRead :=
    unary_cont_closed leftUnary rightUnary symmetricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row symmetricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
              hsame row readbackLeft ∨ hsame row readbackRight ∨
                hsame row symmetricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle symmetricRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro symmetricRead ⟨hsame_refl symmetricRead, symmetricUnary⟩
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
      exact ⟨source.right, provenancePkg, symmetricPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, symmetricUnary⟩

end BEDC.Derived.HyperspaceUp
