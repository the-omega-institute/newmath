import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_namecert_obligation_surface [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont Hs C replayRead →
        PkgSig bundle M pkg →
          SemanticNameCert
              (fun row : BHist => (hsame row M ∨ hsame row replayRead) ∧
                UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                  hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                    hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                      hsame row replayRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
              hsame ∧
            UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier replayRoute localNamePkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, mUnary, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have sourceLocal :
      (fun row : BHist => (hsame row M ∨ hsame row replayRead) ∧ UnaryHistory row)
        M := by
    exact ⟨Or.inl (hsame_refl M), mUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row M ∨ hsame row replayRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                  hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro M sourceLocal
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
          | inl sameLocal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocal)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLocal =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameLocal
      | inr sameReplay =>
          right
          right
          right
          right
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, replayUnary⟩

end BEDC.Derived.HyperspaceUp
