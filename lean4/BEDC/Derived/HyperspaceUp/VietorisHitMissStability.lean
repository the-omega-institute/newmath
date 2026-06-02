import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisHitMissStability [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead directedLeft directedRight
      toleranceRead hitMissRead replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont D0 R directedLeft →
            Cont D1 R directedRight →
              Cont directedLeft directedRight toleranceRead →
                Cont subsetRead toleranceRead hitMissRead →
                  Cont Hs C replayRead →
                    Cont hitMissRead replayRead publicRead →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                                hsame row N0 ∨ hsame row N1 ∨ hsame row D0 ∨
                                  hsame row D1 ∨ hsame row R ∨ hsame row hitMissRead ∨
                                    hsame row replayRead ∨ hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier subsetRoute netRoute directedLeftRoute directedRightRoute toleranceRoute
    hitMissRoute replayRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have _netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have directedLeftUnary : UnaryHistory directedLeft :=
    unary_cont_closed d0Unary rUnary directedLeftRoute
  have directedRightUnary : UnaryHistory directedRight :=
    unary_cont_closed d1Unary rUnary directedRightRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed directedLeftUnary directedRightUnary toleranceRoute
  have hitMissUnary : UnaryHistory hitMissRead :=
    unary_cont_closed subsetUnary toleranceUnary hitMissRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hitMissUnary replayUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row hitMissRead ∨ hsame row replayRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.HyperspaceUp
