import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceBridgedInterfaceRoute [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead hausdorffRead vietorisRead
      completionRead replayRead localRead publicRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactRead ->
        Cont D0 D1 hausdorffRead ->
          Cont N0 N1 vietorisRead ->
            Cont compactRead M completionRead ->
              Cont Hs C replayRead ->
                Cont replayRead M localRead ->
                  Cont localRead P publicRead ->
                    Cont publicRead M bridgeRead ->
                      PkgSig bundle completionRead pkg ->
                        PkgSig bundle localRead pkg ->
                          PkgSig bundle publicRead pkg ->
                            PkgSig bundle bridgeRead pkg ->
                              SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row publicRead ∨ hsame row bridgeRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row compactRead ∨ hsame row hausdorffRead ∨
                                    hsame row vietorisRead ∨ hsame row completionRead ∨
                                      hsame row localRead ∨ hsame row publicRead ∨
                                        hsame row bridgeRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle publicRead pkg ∧
                                      PkgSig bundle bridgeRead pkg)
                                hsame ∧
                                UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier compactRoute hausdorffRoute vietorisRoute completionRoute replayRoute
    localRoute publicRoute bridgeRoute _completionPkg _localPkg publicPkg bridgePkg
  obtain ⟨xUnary, k0Unary, _k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, hsUnary, cUnary, pUnary, mUnary, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed d0Unary d1Unary hausdorffRoute
  have vietorisUnary : UnaryHistory vietorisRead :=
    unary_cont_closed n0Unary n1Unary vietorisRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed compactUnary mUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary mUnary localRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localUnary pUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary mUnary bridgeRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeRead ⟨Or.inr (hsame_refl bridgeRead), bridgeUnary⟩
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
          cases source.left with
          | inl samePublic =>
              exact
                ⟨Or.inl (hsame_trans (hsame_symm sameRows) samePublic),
                  unary_transport source.right sameRows⟩
          | inr sameBridge =>
              exact
                ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameBridge),
                  unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl samePublic =>
            right
            right
            right
            right
            right
            exact Or.inl samePublic
        | inr sameBridge =>
            right
            right
            right
            right
            right
            right
            exact sameBridge
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, publicPkg, bridgePkg⟩
    }
  · exact bridgeUnary

theorem HyperspaceBridgedRouteFormalTarget [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M publicRead bridgeRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont P M publicRead →
        Cont publicRead Hs bridgeRead →
          Cont bridgeRead C targetRead →
            PkgSig bundle targetRead pkg →
              UnaryHistory publicRead ∧ UnaryHistory bridgeRead ∧
                UnaryHistory targetRead ∧ Cont P M publicRead ∧
                  Cont publicRead Hs bridgeRead ∧ Cont bridgeRead C targetRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig UnaryHistory
  intro carrier publicRoute bridgeRoute targetRoute targetPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, pUnary, mUnary, provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed pUnary mUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary hsUnary bridgeRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed bridgeUnary cUnary targetRoute
  exact
    ⟨publicUnary, bridgeUnary, targetUnary, publicRoute, bridgeRoute, targetRoute,
      provenancePkg, targetPkg⟩

end BEDC.Derived.HyperspaceUp
