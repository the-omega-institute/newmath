import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TwinSubstrateBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateBridgeCarrier_replay_stability [AskSetup] [PackageSetup]
    {M G F R L H C P N metaRead groundRead frontierRead replayMeta replayGround
      replayFrontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory F ∧ UnaryHistory R ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      Cont M R metaRead →
        Cont G R groundRead →
          Cont F L frontierRead →
            hsame metaRead replayMeta →
              hsame groundRead replayGround →
                hsame frontierRead replayFrontier →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row replayMeta ∨ hsame row replayGround ∨
                          hsame row replayFrontier)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row G ∨ hsame row F ∨ hsame row R ∨
                          hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row replayMeta ∨
                              hsame row replayGround ∨ hsame row replayFrontier)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M R metaRead ∧ Cont G R groundRead ∧
                          Cont F L frontierRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory replayMeta ∧ UnaryHistory replayGround ∧
                      UnaryHistory replayFrontier := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier metaRoute groundRoute frontierRoute sameMeta sameGround sameFrontier
  obtain ⟨mUnary, gUnary, fUnary, rUnary, lUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, pPkg, nPkg⟩ := carrier
  have metaUnary : UnaryHistory metaRead :=
    unary_cont_closed mUnary rUnary metaRoute
  have groundUnary : UnaryHistory groundRead :=
    unary_cont_closed gUnary rUnary groundRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed fUnary lUnary frontierRoute
  have replayMetaUnary : UnaryHistory replayMeta :=
    unary_transport metaUnary sameMeta
  have replayGroundUnary : UnaryHistory replayGround :=
    unary_transport groundUnary sameGround
  have replayFrontierUnary : UnaryHistory replayFrontier :=
    unary_transport frontierUnary sameFrontier
  have sourceReplayMeta :
      (fun row : BHist =>
        hsame row replayMeta ∨ hsame row replayGround ∨ hsame row replayFrontier)
          replayMeta :=
    Or.inl (hsame_refl replayMeta)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row replayMeta ∨ hsame row replayGround ∨ hsame row replayFrontier)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row F ∨ hsame row R ∨ hsame row L ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayMeta ∨ hsame row replayGround ∨ hsame row replayFrontier)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R metaRead ∧ Cont G R groundRead ∧
              Cont F L frontierRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replayMeta, sourceReplayMeta⟩
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
        cases source with
        | inl sameReplayMeta =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameReplayMeta)
        | inr tail =>
            cases tail with
            | inl sameReplayGround =>
                exact Or.inr
                  (Or.inl (hsame_trans (hsame_symm sameRows) sameReplayGround))
            | inr sameReplayFrontier =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) sameReplayFrontier))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameReplayMeta =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          left
          exact sameReplayMeta
      | inr tail =>
          cases tail with
          | inl sameReplayGround =>
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
              left
              exact sameReplayGround
          | inr sameReplayFrontier =>
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
              exact sameReplayFrontier
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameReplayMeta =>
          exact
            ⟨unary_transport replayMetaUnary (hsame_symm sameReplayMeta), metaRoute,
              groundRoute, frontierRoute, pPkg, nPkg⟩
      | inr tail =>
          cases tail with
          | inl sameReplayGround =>
              exact
                ⟨unary_transport replayGroundUnary (hsame_symm sameReplayGround),
                  metaRoute, groundRoute, frontierRoute, pPkg, nPkg⟩
          | inr sameReplayFrontier =>
              exact
                ⟨unary_transport replayFrontierUnary (hsame_symm sameReplayFrontier),
                  metaRoute, groundRoute, frontierRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, replayMetaUnary, replayGroundUnary, replayFrontierUnary⟩

end BEDC.Derived.TwinSubstrateBridgeUp
