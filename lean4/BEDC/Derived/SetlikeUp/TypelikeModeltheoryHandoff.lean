import BEDC.Derived.SetlikeUp.RootNameCertObligations

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeTypelikeModeltheoryHandoff [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay
      extensionalReplay routeRead namedRead typeFamilyRead firstOrderRead modelRead
      handoffRead : BHist}
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
                                    Cont namedRead P typeFamilyRead ->
                                      Cont namedRead H firstOrderRead ->
                                        Cont namedRead C modelRead ->
                                          Cont firstOrderRead modelRead handoffRead ->
                                            PkgSig bundle P pkg ->
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row handoffRead ∧ UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row M ∨ hsame row Q ∨
                                                      hsame row I ∨ hsame row R ∨
                                                        hsame row E ∨ hsame row namedRead ∨
                                                          hsame row typeFamilyRead ∨
                                                            hsame row firstOrderRead ∨
                                                              hsame row modelRead ∨
                                                                hsame row handoffRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      Cont namedRead P typeFamilyRead ∧
                                                        Cont namedRead H firstOrderRead ∧
                                                          Cont namedRead C modelRead ∧
                                                            Cont firstOrderRead modelRead
                                                              handoffRead ∧
                                                              PkgSig bundle P pkg)
                                                  hsame ∧
                                                UnaryHistory typeFamilyRead ∧
                                                  UnaryHistory firstOrderRead ∧
                                                    UnaryHistory modelRead ∧
                                                      UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC rowsP rowsN membershipRoute
    subsetRoute comprehensionRoute extensionalRoute routeRoute namedRoute typeFamilyRoute
    firstOrderRoute modelRoute handoffRoute packageRead
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
    unary_cont_closed extensionalUnary comprehensionUnary routeRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary rowsN namedRoute
  have typeFamilyUnary : UnaryHistory typeFamilyRead :=
    unary_cont_closed namedUnary rowsP typeFamilyRoute
  have firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed namedUnary rowsH firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed namedUnary rowsC modelRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed firstOrderUnary modelUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row namedRead ∨ hsame row typeFamilyRead ∨ hsame row firstOrderRead ∨
                hsame row modelRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont namedRead P typeFamilyRead ∧
              Cont namedRead H firstOrderRead ∧ Cont namedRead C modelRead ∧
                Cont firstOrderRead modelRead handoffRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, typeFamilyRoute, firstOrderRoute, modelRoute, handoffRoute,
          packageRead⟩
  }
  exact ⟨cert, typeFamilyUnary, firstOrderUnary, modelUnary, handoffUnary⟩

end BEDC.Derived.SetlikeUp
