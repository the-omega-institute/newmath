import BEDC.Derived.BoundedSetUp.BallContainmentRoute
import BEDC.Derived.BoundedSetUp.DiameterConsumerBoundary

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_metric_ball_handoff [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      diameterRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay diameterRead ->
            Cont diameterRead nameRow handoffRead ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row ball ∨ hsame row ballRead ∨ hsame row diameterRead ∨
                        Cont diameterRead nameRow handoffRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg ∧
                        hsame row handoffRead)
                    hsame ∧
                  UnaryHistory memberRead ∧ UnaryHistory ballRead ∧
                    UnaryHistory diameterRead ∧ UnaryHistory handoffRead ∧
                      Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                        Cont ballRead replay diameterRead ∧
                          Cont diameterRead nameRow handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius ballReplayDiameter diameterNameHandoff handoffPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    replayUnary, provenanceUnary, nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have diameterUnary : UnaryHistory diameterRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayDiameter
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed diameterUnary nameUnary diameterNameHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ball ∨ hsame row ballRead ∨ hsame row diameterRead ∨
              Cont diameterRead nameRow handoffRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg ∧
              hsame row handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr diameterNameHandoff))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, handoffPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, diameterUnary, handoffUnary, subsetCenter,
      memberRadius, ballReplayDiameter, diameterNameHandoff⟩

end BEDC.Derived.BoundedSetUp
