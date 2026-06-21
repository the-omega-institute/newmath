import BEDC.Derived.SetlikeUp.RootNameCertObligations

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeFamilyFiberModelSatisfactionRoute [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      familyReplay satisfactionReplay namedReplay : BHist}
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
                                Cont extensionalReplay H familyReplay ->
                                  Cont familyReplay C satisfactionReplay ->
                                    Cont satisfactionReplay N namedReplay ->
                                      PkgSig bundle P pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedReplay ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row Q ∨
                                                hsame row I ∨ hsame row R ∨
                                                  hsame row E ∨ hsame row H ∨
                                                    hsame row C ∨ hsame row P ∨
                                                      hsame row N ∨
                                                        hsame row membershipReplay ∨
                                                          hsame row subsetReplay ∨
                                                            hsame row comprehensionReplay ∨
                                                              hsame row extensionalReplay ∨
                                                                hsame row familyReplay ∨
                                                                  hsame row satisfactionReplay ∨
                                                                    hsame row namedReplay)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont M Q membershipReplay ∧
                                                  Cont Q I subsetReplay ∧
                                                    Cont R E comprehensionReplay ∧
                                                      Cont membershipReplay subsetReplay
                                                        extensionalReplay ∧
                                                        Cont extensionalReplay H
                                                          familyReplay ∧
                                                          Cont familyReplay C
                                                            satisfactionReplay ∧
                                                            Cont satisfactionReplay N
                                                              namedReplay ∧
                                                              PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory membershipReplay ∧
                                            UnaryHistory subsetReplay ∧
                                              UnaryHistory comprehensionReplay ∧
                                                UnaryHistory extensionalReplay ∧
                                                  UnaryHistory familyReplay ∧
                                                    UnaryHistory satisfactionReplay ∧
                                                      UnaryHistory namedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC rowsP rowsN membershipRoute
    subsetRoute comprehensionRoute extensionalRoute familyRoute satisfactionRoute namedRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have familyUnary : UnaryHistory familyReplay :=
    unary_cont_closed extensionalUnary rowsH familyRoute
  have satisfactionUnary : UnaryHistory satisfactionReplay :=
    unary_cont_closed familyUnary rowsC satisfactionRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed satisfactionUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row membershipReplay ∨ hsame row subsetReplay ∨
                  hsame row comprehensionReplay ∨ hsame row extensionalReplay ∨
                    hsame row familyReplay ∨ hsame row satisfactionReplay ∨
                      hsame row namedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ Cont Q I subsetReplay ∧
              Cont R E comprehensionReplay ∧
                Cont membershipReplay subsetReplay extensionalReplay ∧
                  Cont extensionalReplay H familyReplay ∧
                    Cont familyReplay C satisfactionReplay ∧
                      Cont satisfactionReplay N namedReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedReplay ⟨hsame_refl namedReplay, namedUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          familyRoute, satisfactionRoute, namedRoute, packageRead⟩
  }
  exact
    ⟨cert, membershipUnary, subsetUnary, comprehensionUnary, extensionalUnary,
      familyUnary, satisfactionUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
