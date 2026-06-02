import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisRootUnblockObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M X' K0' K1' N0' N1' D0' D1' R' Hs' C' P'
      M' subsetRead netRead directedLeft directedRight toleranceRead hitMissRead
      replayRead publicRead refinedHit refinedMiss refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      HyperspaceCarrier X' K0' K1' N0' N1' D0' D1' R' Hs' C' P' M' bundle pkg →
        Cont K0 K1 subsetRead →
          Cont N0 N1 netRead →
            Cont D0 R directedLeft →
              Cont D1 R directedRight →
                Cont directedLeft directedRight toleranceRead →
                  Cont subsetRead toleranceRead hitMissRead →
                    Cont Hs C replayRead →
                      Cont hitMissRead replayRead publicRead →
                        hsame X' X →
                          hsame K0' K0 →
                            hsame K1' K1 →
                              Cont D0' D0 refinedHit →
                                Cont D1' D1 refinedMiss →
                                  Cont refinedHit refinedMiss refinedRead →
                                    PkgSig bundle publicRead pkg →
                                      PkgSig bundle refinedRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row refinedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row X ∨ hsame row K0 ∨
                                                hsame row K1 ∨ hsame row D0 ∨
                                                  hsame row D1 ∨ hsame row hitMissRead ∨
                                                    hsame row publicRead ∨
                                                      hsame row refinedHit ∨
                                                        hsame row refinedMiss ∨
                                                          hsame row refinedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont D0' D0 refinedHit ∧
                                                  Cont D1' D1 refinedMiss ∧
                                                    Cont refinedHit refinedMiss
                                                      refinedRead ∧
                                                      PkgSig bundle refinedRead pkg)
                                            hsame ∧
                                          UnaryHistory publicRead ∧
                                            UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier carrier' subsetRoute netRoute directedLeftRoute directedRightRoute
    toleranceRoute hitMissRoute replayRoute publicRoute _sameX _sameK0 _sameK1
    refinedHitRoute refinedMissRoute refinedReadRoute _publicPkg refinedPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary, rUnary,
    hsUnary, cUnary, _pUnary, _mUnary, _provenancePkg⟩ := carrier
  obtain ⟨_x'Unary, _k0'Unary, _k1'Unary, _n0'Unary, _n1'Unary, d0'Unary,
    d1'Unary, _r'Unary, _hs'Unary, _c'Unary, _p'Unary, _m'Unary,
    _provenancePkg'⟩ := carrier'
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
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
  have refinedHitUnary : UnaryHistory refinedHit :=
    unary_cont_closed d0'Unary d0Unary refinedHitRoute
  have refinedMissUnary : UnaryHistory refinedMiss :=
    unary_cont_closed d1'Unary d1Unary refinedMissRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed refinedHitUnary refinedMissUnary refinedReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨
              hsame row D1 ∨ hsame row hitMissRead ∨ hsame row publicRead ∨
                hsame row refinedHit ∨ hsame row refinedMiss ∨ hsame row refinedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D0' D0 refinedHit ∧ Cont D1' D1 refinedMiss ∧
              Cont refinedHit refinedMiss refinedRead ∧ PkgSig bundle refinedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedReadUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refinedHitRoute, refinedMissRoute, refinedReadRoute, refinedPkg⟩
  }
  exact ⟨cert, publicUnary, refinedReadUnary⟩

end BEDC.Derived.HyperspaceUp
