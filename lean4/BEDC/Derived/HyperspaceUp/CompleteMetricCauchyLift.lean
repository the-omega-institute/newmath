import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompleteMetricCauchyLift [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead directedRead cauchyRead
      replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont D0 D1 directedRead →
            Cont directedRead R cauchyRead →
              Cont Hs C replayRead →
                PkgSig bundle cauchyRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row cauchyRead ∨ hsame row replayRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                          hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                            hsame row Hs ∨ hsame row C ∨ hsame row P ∨
                              hsame row M ∨ hsame row subsetRead ∨
                                hsame row netRead ∨ hsame row directedRead ∨
                                  hsame row cauchyRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle cauchyRead pkg)
                      hsame ∧
                    UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                      UnaryHistory directedRead ∧ UnaryHistory cauchyRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle PkgSig
  intro carrier subsetRoute netRoute directedRoute cauchyRoute replayRoute cauchyPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    hsUnary, cUnary, _provenanceUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed directedUnary rUnary cauchyRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row cauchyRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                  hsame row subsetRead ∨ hsame row netRead ∨
                    hsame row directedRead ∨ hsame row cauchyRead ∨
                      hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro cauchyRead ⟨Or.inl (hsame_refl cauchyRead), cauchyUnary⟩
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
          | inl sameCauchy =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCauchy)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCauchy =>
          right; right; right; right; right; right; right; right; right; right
          right; right; right; right; right
          exact Or.inl sameCauchy
      | inr sameReplay =>
          right; right; right; right; right; right; right; right; right; right
          right; right; right; right; right
          exact Or.inr sameReplay
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, cauchyPkg⟩
  }
  exact ⟨cert, subsetUnary, netUnary, directedUnary, cauchyUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
