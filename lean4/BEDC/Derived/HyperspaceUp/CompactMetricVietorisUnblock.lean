import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCompactMetricVietorisUnblock [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactSource subsetRead netRead distanceRead
      hitMissRead vietorisRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont X K0 compactSource →
        Cont compactSource K1 subsetRead →
          Cont N0 N1 netRead →
            Cont D0 D1 distanceRead →
              Cont subsetRead distanceRead hitMissRead →
                Cont hitMissRead R vietorisRead →
                  Cont Hs C replayRead →
                    PkgSig bundle vietorisRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row vietorisRead ∨ hsame row replayRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                              hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                                hsame row D1 ∨ hsame row R ∨ hsame row compactSource ∨
                                  hsame row subsetRead ∨ hsame row netRead ∨
                                    hsame row distanceRead ∨ hsame row hitMissRead ∨
                                      hsame row vietorisRead ∨ hsame row replayRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle vietorisRead pkg)
                          hsame ∧
                        UnaryHistory compactSource ∧ UnaryHistory subsetRead ∧
                          UnaryHistory netRead ∧ UnaryHistory distanceRead ∧
                            UnaryHistory hitMissRead ∧ UnaryHistory vietorisRead ∧
                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier compactRoute subsetRoute netRoute distanceRoute hitMissRoute vietorisRoute
    replayRoute vietorisPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    rUnary, hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactSource :=
    unary_cont_closed xUnary k0Unary compactRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed compactUnary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have hitMissUnary : UnaryHistory hitMissRead :=
    unary_cont_closed subsetUnary distanceUnary hitMissRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed hitMissUnary rUnary vietorisRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have sourceVietoris :
      (fun row : BHist =>
        (hsame row vietorisRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          vietorisRead := by
    exact ⟨Or.inl (hsame_refl vietorisRead), vietorisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row vietorisRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row compactSource ∨ hsame row subsetRead ∨ hsame row netRead ∨
                  hsame row distanceRead ∨ hsame row hitMissRead ∨
                    hsame row vietorisRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle vietorisRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro vietorisRead sourceVietoris
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
          | inl sameVietoris =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameVietoris)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameVietoris =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl sameVietoris)))))))))))))
      | inr sameReplay =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr sameReplay)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, vietorisPkg⟩
  }
  exact
    ⟨cert, compactUnary, subsetUnary, netUnary, distanceUnary, hitMissUnary, vietorisUnary,
      replayUnary⟩

end BEDC.Derived.HyperspaceUp
