import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRootVietorisNetBasis [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead hitMissRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont subsetRead netRead hitMissRead →
            Cont Hs C replayRead →
              PkgSig bundle hitMissRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row hitMissRead ∨ hsame row replayRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                        hsame row N1 ∨ hsame row subsetRead ∨ hsame row netRead ∨
                          hsame row hitMissRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle hitMissRead pkg)
                    hsame ∧
                  UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                    UnaryHistory hitMissRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier subsetRoute netRoute hitMissRoute replayRoute hitMissPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have hitMissUnary : UnaryHistory hitMissRead :=
    unary_cont_closed subsetUnary netUnary hitMissRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row hitMissRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row subsetRead ∨ hsame row netRead ∨
                hsame row hitMissRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle hitMissRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hitMissRead ⟨Or.inl (hsame_refl hitMissRead), hitMissUnary⟩
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
        constructor
        · cases source.left with
          | inl sameHitMiss =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameHitMiss)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameHitMiss =>
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameHitMiss
      | inr sameReplay =>
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr sameReplay
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, hitMissPkg⟩
  }
  exact ⟨cert, subsetUnary, netUnary, hitMissUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
