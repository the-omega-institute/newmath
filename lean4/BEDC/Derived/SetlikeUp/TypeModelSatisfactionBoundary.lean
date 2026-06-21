import BEDC.Derived.SetlikeUp.TypelikeModeltheoryHandoff

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeTypeModelSatisfactionBoundary [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay satisfactionReplay
      namedReplay typeFamilyRead firstOrderRead modelRead boundaryRead : BHist}
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
                              Cont membershipReplay subsetReplay satisfactionReplay ->
                                Cont satisfactionReplay N namedReplay ->
                                  Cont namedReplay P typeFamilyRead ->
                                    Cont namedReplay H firstOrderRead ->
                                      Cont namedReplay C modelRead ->
                                        Cont typeFamilyRead modelRead boundaryRead ->
                                          PkgSig bundle P pkg ->
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row boundaryRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row M ∨ hsame row Q ∨
                                                    hsame row I ∨ hsame row R ∨
                                                      hsame row E ∨ hsame row namedReplay ∨
                                                        hsame row typeFamilyRead ∨
                                                          hsame row firstOrderRead ∨
                                                            hsame row modelRead ∨
                                                              hsame row boundaryRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    Cont namedReplay P typeFamilyRead ∧
                                                      Cont namedReplay H firstOrderRead ∧
                                                        Cont namedReplay C modelRead ∧
                                                          Cont typeFamilyRead modelRead
                                                            boundaryRead ∧
                                                            PkgSig bundle P pkg)
                                                hsame ∧
                                              UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC rowsP rowsN membershipRoute
    subsetRoute comprehensionRoute satisfactionRoute namedRoute typeFamilyRoute
    firstOrderRoute modelRoute boundaryRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have _comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have satisfactionUnary : UnaryHistory satisfactionReplay :=
    unary_cont_closed membershipUnary subsetUnary satisfactionRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed satisfactionUnary rowsN namedRoute
  have typeFamilyUnary : UnaryHistory typeFamilyRead :=
    unary_cont_closed namedUnary rowsP typeFamilyRoute
  have _firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed namedUnary rowsH firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed namedUnary rowsC modelRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed typeFamilyUnary modelUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row namedReplay ∨ hsame row typeFamilyRead ∨
                hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont namedReplay P typeFamilyRead ∧
              Cont namedReplay H firstOrderRead ∧ Cont namedReplay C modelRead ∧
                Cont typeFamilyRead modelRead boundaryRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
        ⟨source.right, typeFamilyRoute, firstOrderRoute, modelRoute, boundaryRoute,
          packageRead⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.SetlikeUp
