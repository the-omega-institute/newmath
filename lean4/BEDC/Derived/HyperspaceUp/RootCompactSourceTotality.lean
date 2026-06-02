import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRootCompactSourceTotality [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactSourceRead hitMissRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactSourceRead ->
        Cont compactSourceRead K1 hitMissRead ->
          PkgSig bundle hitMissRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row hitMissRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                    hsame row compactSourceRead ∨ hsame row hitMissRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle hitMissRead pkg)
                hsame ∧
              UnaryHistory compactSourceRead ∧ UnaryHistory hitMissRead ∧
                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle Pkg SemanticNameCert
  intro carrier compactRoute hitMissRoute hitMissPkg
  obtain ⟨xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, _d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactSourceRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have hitMissUnary : UnaryHistory hitMissRead :=
    unary_cont_closed compactUnary k1Unary hitMissRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hitMissRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
              hsame row compactSourceRead ∨ hsame row hitMissRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle hitMissRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hitMissRead ⟨hsame_refl hitMissRead, hitMissUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, hitMissPkg⟩
  }
  exact ⟨cert, compactUnary, hitMissUnary, provenancePkg⟩

end BEDC.Derived.HyperspaceUp
