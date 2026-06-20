import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeRootMembershipTripleUnblock [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay firstOrderRead modelRead typeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                Cont M Q membershipReplay ->
                  Cont membershipReplay H firstOrderRead ->
                    Cont membershipReplay C modelRead ->
                      Cont membershipReplay P typeRead ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row firstOrderRead ∨ hsame row modelRead ∨
                                  hsame row typeRead)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
                                  hsame row firstOrderRead ∨ hsame row modelRead ∨
                                    hsame row typeRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                  PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory membershipReplay ∧ UnaryHistory firstOrderRead ∧
                              UnaryHistory modelRead ∧ UnaryHistory typeRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP membershipRoute firstOrderRoute modelRoute
    typeRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed membershipUnary rowsH firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed membershipUnary rowsC modelRoute
  have typeUnary : UnaryHistory typeRead :=
    unary_cont_closed membershipUnary rowsP typeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row typeRead)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
              hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row typeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro firstOrderRead (Or.inl (hsame_refl firstOrderRead))
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
        intro row other sameRows source
        cases source with
        | inl firstSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) firstSource)
        | inr tail =>
            cases tail with
            | inl modelSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) modelSource))
            | inr typeSource =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) typeSource))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl firstSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inl firstSource)))
      | inr tail =>
          cases tail with
          | inl modelSource =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl modelSource))))
          | inr typeSource =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr typeSource))))
    ledger_sound := by
      intro row source
      cases source with
      | inl firstSource =>
          exact
            ⟨unary_transport firstOrderUnary (hsame_symm firstSource), membershipRoute,
              packageRead⟩
      | inr tail =>
          cases tail with
          | inl modelSource =>
              exact
                ⟨unary_transport modelUnary (hsame_symm modelSource), membershipRoute,
                  packageRead⟩
          | inr typeSource =>
              exact
                ⟨unary_transport typeUnary (hsame_symm typeSource), membershipRoute,
                  packageRead⟩
  }
  exact ⟨cert, membershipUnary, firstOrderUnary, modelUnary, typeUnary⟩

theorem SetlikeRootMembershipSourceTriple [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay firstOrderRead modelRead typeRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont M Q membershipReplay ->
                    Cont membershipReplay H firstOrderRead ->
                      Cont membershipReplay C modelRead ->
                        Cont membershipReplay P typeRead ->
                          Cont typeRead N namedRead ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨
                                      hsame row membershipReplay ∨
                                        hsame row firstOrderRead ∨ hsame row modelRead ∨
                                          hsame row typeRead ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                      PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory membershipReplay ∧
                                  UnaryHistory firstOrderRead ∧
                                    UnaryHistory modelRead ∧
                                      UnaryHistory typeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP rowsN membershipRoute firstOrderRoute
    modelRoute typeRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed membershipUnary rowsH firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed membershipUnary rowsC modelRoute
  have typeUnary : UnaryHistory typeRead :=
    unary_cont_closed membershipUnary rowsP typeRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed typeUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
              hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row typeRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, membershipRoute, packageRead⟩
  }
  exact ⟨cert, membershipUnary, firstOrderUnary, modelUnary, typeUnary, namedUnary⟩

theorem SetlikeRootComprehensionLedgerTriple [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M -> UnaryHistory Q -> UnaryHistory I -> UnaryHistory R ->
        UnaryHistory E -> UnaryHistory H -> UnaryHistory N ->
          Cont M Q membershipReplay -> Cont Q I subsetReplay ->
            Cont R E comprehensionReplay ->
              Cont membershipReplay subsetReplay extensionalReplay ->
                Cont extensionalReplay comprehensionReplay routeRead ->
                  Cont routeRead N namedRead -> PkgSig bundle P pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
                            hsame row E ∨ hsame row routeRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont extensionalReplay comprehensionReplay routeRead ∧
                            Cont routeRead N namedRead ∧ PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory membershipReplay ∧ UnaryHistory subsetReplay ∧
                        UnaryHistory comprehensionReplay ∧ UnaryHistory extensionalReplay ∧
                          UnaryHistory routeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE _rowsH rowsN membershipRoute subsetRoute
    comprehensionRoute extensionalRoute routeReadRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed extensionalUnary comprehensionUnary routeReadRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row routeRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont extensionalReplay comprehensionReplay routeRead ∧
              Cont routeRead N namedRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeReadRoute, namedRoute, packageRead⟩
  }
  exact
    ⟨cert, membershipUnary, subsetUnary, comprehensionUnary, extensionalUnary, routeUnary,
      namedUnary⟩

theorem SetlikeTypeModelMembershipEnvelope [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead namedRead firstOrderRead modelRead typeRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont M Q membershipReplay ->
                          Cont Q I subsetReplay ->
                            Cont R E comprehensionReplay ->
                              Cont membershipReplay subsetReplay extensionalReplay ->
                                Cont extensionalReplay comprehensionReplay routeRead ->
                                  Cont routeRead N namedRead ->
                                    Cont namedRead H firstOrderRead ->
                                      Cont namedRead C modelRead ->
                                        Cont namedRead P typeRead ->
                                          Cont typeRead N publicRead ->
                                            PkgSig bundle P pkg ->
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row publicRead ∧ UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                                      hsame row R ∨ hsame row E ∨
                                                        hsame row namedRead ∨
                                                          hsame row publicRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      Cont routeRead N namedRead ∧
                                                        Cont typeRead N publicRead ∧
                                                          PkgSig bundle P pkg)
                                                  hsame ∧
                                                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC rowsP rowsN membershipRoute
    subsetRoute comprehensionRoute extensionalRoute routeReadRoute namedRoute firstOrderRoute
    modelRoute typeRoute publicRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed extensionalUnary comprehensionUnary routeReadRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary rowsN namedRoute
  have _firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed namedUnary rowsH firstOrderRoute
  have _modelUnary : UnaryHistory modelRead :=
    unary_cont_closed namedUnary rowsC modelRoute
  have typeUnary : UnaryHistory typeRead :=
    unary_cont_closed namedUnary rowsP typeRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed typeUnary rowsN publicRoute
  have sourceAtPublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row namedRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont routeRead N namedRead ∧ Cont typeRead N publicRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namedRoute, publicRoute, packageRead⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SetlikeUp
