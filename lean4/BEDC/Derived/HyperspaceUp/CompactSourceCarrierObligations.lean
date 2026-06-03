import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompactSourceCarrierObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead netRead supportRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont X K0 compactRead →
        Cont K1 N1 netRead →
          Cont compactRead netRead supportRead →
            Cont Hs supportRead replayRead →
              PkgSig bundle replayRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                        hsame row N0 ∨ hsame row N1 ∨ hsame row supportRead ∨
                          hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle replayRead pkg)
                    hsame ∧
                  UnaryHistory supportRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier compactRoute netRoute supportRoute replayRoute replayPkg
  obtain ⟨xUnary, k0Unary, k1Unary, _n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed k1Unary n1Unary netRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed compactUnary netUnary supportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary supportUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row supportRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, replayPkg⟩
  }
  exact ⟨cert, supportUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
