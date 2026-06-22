import BEDC.Derived.ClosedNormalConfluenceSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.MetaCIC.Beta.Conversion

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.MetaCIC

theorem ClosedNormalConfluenceSealNormalSource
    {source normal routeLeft routeRight join transports continuations provenance nameCert :
      BHist}
    {t u v : Term}
    (normalSource : BetaStrong t)
    (leftRoute : BetaStarStep t u)
    (rightRoute : BetaStarStep t v) :
    (∃ w : Term, BetaStarStep u w ∧ BetaStarStep v w) ∧
      closedNormalConfluenceSealToEventFlow
          (ClosedNormalConfluenceSealUp.mk source normal routeLeft routeRight join
            transports continuations provenance nameCert) ≠
        [] := by
  -- BEDC touchpoint anchor: BHist BetaStrong BetaStarStep ClosedNormalConfluenceSealUp
  have betaNormal : BetaNormal t := betaNormal_of_betaStrong normalSource
  have leftBack : BetaStarStep u t :=
    betaStarStep_of_normal_source betaNormal leftRoute
  have rightBack : BetaStarStep v t :=
    betaStarStep_of_normal_source betaNormal rightRoute
  constructor
  · exact ⟨t, leftBack, rightBack⟩
  · intro h
    cases h

theorem ClosedNormalConfluenceSealObligationSurface [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory normal →
        UnaryHistory routeRight →
          UnaryHistory transports →
            Cont source normal routeLeft →
              Cont routeLeft routeRight join →
                Cont join transports obligationRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle obligationRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                hsame row routeRight ∨ hsame row join ∨
                                  hsame row obligationRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                              hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                                hsame row continuations ∨ hsame row provenance ∨
                                  hsame row nameCert ∨ hsame row obligationRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont source normal routeLeft ∧
                              Cont routeLeft routeRight join ∧
                                Cont join transports obligationRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle obligationRead pkg)
                          hsame ∧
                        UnaryHistory routeLeft ∧ UnaryHistory join ∧
                          UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary normalUnary routeRightUnary transportsUnary sourceNormalRoute
    routeJoin obligationRoute provenancePkg obligationPkg
  have routeLeftUnary : UnaryHistory routeLeft :=
    unary_cont_closed sourceUnary normalUnary sourceNormalRoute
  have joinUnary : UnaryHistory join :=
    unary_cont_closed routeLeftUnary routeRightUnary routeJoin
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed joinUnary transportsUnary obligationRoute
  have obligationSource :
      (fun row : BHist =>
        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
            hsame row routeRight ∨ hsame row join ∨ hsame row obligationRead) ∧
          UnaryHistory row) obligationRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (hsame_refl obligationRead))))),
        obligationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                hsame row routeRight ∨ hsame row join ∨ hsame row obligationRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
              hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                hsame row continuations ∨ hsame row provenance ∨ hsame row nameCert ∨
                  hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source normal routeLeft ∧
              Cont routeLeft routeRight join ∧ Cont join transports obligationRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead obligationSource
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
        intro _row _other sameRows sourceRow
        have transportedUnary : UnaryHistory _ :=
          unary_transport sourceRow.right sameRows
        cases sourceRow.left with
        | inl sameSource =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSource), transportedUnary⟩
        | inr rest₁ =>
            cases rest₁ with
            | inl sameNormal =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)),
                    transportedUnary⟩
            | inr rest₂ =>
                cases rest₂ with
                | inl sameRouteLeft =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameRouteLeft))),
                        transportedUnary⟩
                | inr rest₃ =>
                    cases rest₃ with
                    | inl sameRouteRight =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameRouteRight)))),
                            transportedUnary⟩
                    | inr rest₄ =>
                        cases rest₄ with
                        | inl sameJoin =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameJoin))))),
                                transportedUnary⟩
                        | inr sameObligation =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameObligation))))),
                                transportedUnary⟩
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameSource =>
          exact Or.inl sameSource
      | inr rest₁ =>
          cases rest₁ with
          | inl sameNormal =>
              exact Or.inr (Or.inl sameNormal)
          | inr rest₂ =>
              cases rest₂ with
              | inl sameRouteLeft =>
                  exact Or.inr (Or.inr (Or.inl sameRouteLeft))
              | inr rest₃ =>
                  cases rest₃ with
                  | inl sameRouteRight =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameRouteRight)))
                  | inr rest₄ =>
                      cases rest₄ with
                      | inl sameJoin =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameJoin))))
                      | inr sameObligation =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr sameObligation))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sourceNormalRoute, routeJoin, obligationRoute, provenancePkg,
          obligationPkg⟩
  }
  exact ⟨cert, routeLeftUnary, joinUnary, obligationUnary⟩

theorem ClosedNormalConfluenceSealKernelScope [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory normal →
        UnaryHistory routeRight →
          UnaryHistory transports →
            UnaryHistory continuations →
              UnaryHistory provenance →
                Cont source normal routeLeft →
                  Cont routeLeft routeRight join →
                    Cont continuations provenance scopeRead →
                      PkgSig bundle scopeRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                  hsame row routeRight ∨ hsame row join ∨
                                    hsame row transports ∨ hsame row continuations ∨
                                      hsame row scopeRead) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                hsame row routeRight ∨ hsame row join ∨
                                  hsame row transports ∨ hsame row continuations ∨
                                    hsame row provenance ∨ hsame row nameCert ∨
                                      hsame row scopeRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont source normal routeLeft ∧
                                Cont routeLeft routeRight join ∧
                                  Cont continuations provenance scopeRead ∧
                                    PkgSig bundle scopeRead pkg)
                            hsame ∧
                          UnaryHistory routeLeft ∧ UnaryHistory join ∧
                            UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary normalUnary routeRightUnary transportsUnary continuationsUnary
    provenanceUnary sourceNormalRoute routeJoin scopeRoute scopePkg
  have routeLeftUnary : UnaryHistory routeLeft :=
    unary_cont_closed sourceUnary normalUnary sourceNormalRoute
  have joinUnary : UnaryHistory join :=
    unary_cont_closed routeLeftUnary routeRightUnary routeJoin
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed continuationsUnary provenanceUnary scopeRoute
  have scopeSource :
      (fun row : BHist =>
        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
            hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
              hsame row continuations ∨ hsame row scopeRead) ∧
          UnaryHistory row) scopeRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (hsame_refl scopeRead))))))),
        scopeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                  hsame row continuations ∨ hsame row scopeRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
              hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                hsame row continuations ∨ hsame row provenance ∨ hsame row nameCert ∨
                  hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source normal routeLeft ∧
              Cont routeLeft routeRight join ∧ Cont continuations provenance scopeRead ∧
                PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead scopeSource
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
        intro _row _other sameRows sourceRow
        have transportedUnary : UnaryHistory _ :=
          unary_transport sourceRow.right sameRows
        cases sourceRow.left with
        | inl sameSource =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSource), transportedUnary⟩
        | inr rest₁ =>
            cases rest₁ with
            | inl sameNormal =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)),
                    transportedUnary⟩
            | inr rest₂ =>
                cases rest₂ with
                | inl sameRouteLeft =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameRouteLeft))),
                        transportedUnary⟩
                | inr rest₃ =>
                    cases rest₃ with
                    | inl sameRouteRight =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameRouteRight)))),
                            transportedUnary⟩
                    | inr rest₄ =>
                        cases rest₄ with
                        | inl sameJoin =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameJoin))))),
                                transportedUnary⟩
                        | inr rest₅ =>
                            cases rest₅ with
                            | inl sameTransports =>
                                exact
                                  ⟨Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameTransports)))))),
                                    transportedUnary⟩
                            | inr rest₆ =>
                                cases rest₆ with
                                | inl sameContinuations =>
                                    exact
                                      ⟨Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm sameRows)
                                                        sameContinuations))))))),
                                        transportedUnary⟩
                                | inr sameScope =>
                                    exact
                                      ⟨Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (hsame_trans (hsame_symm sameRows)
                                                        sameScope))))))),
                                        transportedUnary⟩
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameSource =>
          exact Or.inl sameSource
      | inr rest₁ =>
          cases rest₁ with
          | inl sameNormal =>
              exact Or.inr (Or.inl sameNormal)
          | inr rest₂ =>
              cases rest₂ with
              | inl sameRouteLeft =>
                  exact Or.inr (Or.inr (Or.inl sameRouteLeft))
              | inr rest₃ =>
                  cases rest₃ with
                  | inl sameRouteRight =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameRouteRight)))
                  | inr rest₄ =>
                      cases rest₄ with
                      | inl sameJoin =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameJoin))))
                      | inr rest₅ =>
                          cases rest₅ with
                          | inl sameTransports =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr (Or.inl sameTransports)))))
                          | inr rest₆ =>
                              cases rest₆ with
                              | inl sameContinuations =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr (Or.inl sameContinuations))))))
                              | inr sameScope =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr sameScope))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sourceNormalRoute, routeJoin, scopeRoute, scopePkg⟩
  }
  exact ⟨cert, routeLeftUnary, joinUnary, scopeUnary⟩

theorem ClosedNormalConfluenceSealRouteStability
    {source normal routeLeft routeRight join transports continuations provenance nameCert
      source' normal' routeLeft' routeRight' join' transports' continuations' provenance'
      nameCert' replay replay' : BHist} :
    hsame source source' →
      hsame normal normal' →
        hsame routeLeft routeLeft' →
          hsame routeRight routeRight' →
            hsame join join' →
              hsame transports transports' →
                hsame continuations continuations' →
                  hsame provenance provenance' →
                    hsame nameCert nameCert' →
                      Cont source normal routeLeft →
                        Cont routeLeft routeRight join →
                          Cont continuations provenance replay →
                            Cont source' normal' routeLeft' →
                              Cont routeLeft' routeRight' join' →
                                Cont continuations' provenance' replay' →
                                  hsame replay replay' ∧ hsame join join' ∧
                                    hsame routeLeft routeLeft' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ClosedNormalConfluenceSealUp
  intro _sameSource _sameNormal sameRouteLeft _sameRouteRight sameJoin _sameTransports
    sameContinuations sameProvenance _sameNameCert _sourceRoute _joinRoute replayRoute
    _sourceRoute' _joinRoute' replayRoute'
  have replaySame : hsame replay replay' :=
    cont_respects_hsame sameContinuations sameProvenance replayRoute replayRoute'
  exact ⟨replaySame, sameJoin, sameRouteLeft⟩

theorem ClosedNormalConfluenceSealBoundaryNonescape
    {source normal routeLeft routeRight join transports continuations provenance nameCert
      boundaryRead : BHist} :
    Cont source normal routeLeft →
      Cont routeLeft routeRight join →
        Cont join transports boundaryRead →
          hsame boundaryRead boundaryRead ∧ hsame join join ∧ hsame routeLeft routeLeft := by
  -- BEDC touchpoint anchor: BHist Cont hsame ClosedNormalConfluenceSealUp
  intro sourceRoute joinRoute boundaryRoute
  have boundarySame : hsame boundaryRead boundaryRead :=
    cont_deterministic boundaryRoute boundaryRoute
  have joinSame : hsame join join :=
    cont_deterministic joinRoute joinRoute
  have routeLeftSame : hsame routeLeft routeLeft :=
    cont_deterministic sourceRoute sourceRoute
  exact ⟨boundarySame, joinSame, routeLeftSame⟩

end BEDC.Derived.ClosedNormalConfluenceSealUp
