import BEDC.Derived.SetlikeUp.RootNameCertObligations

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeMembershipFamilyBHistInduction [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead comprehensionRead familyRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory N ->
                    Cont M Q membershipRead ->
                      Cont Q I subsetRead ->
                        Cont R E comprehensionRead ->
                          Cont subsetRead comprehensionRead familyRead ->
                            Cont familyRead H namedRead ->
                              PkgSig bundle P pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                        hsame row R ∨ hsame row E ∨ hsame row familyRead ∨
                                          hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont M Q membershipRead ∧
                                        Cont Q I subsetRead ∧
                                          Cont R E comprehensionRead ∧
                                            Cont subsetRead comprehensionRead familyRead ∧
                                              Cont familyRead H namedRead ∧
                                                PkgSig bundle P pkg)
                                    hsame ∧
                                  UnaryHistory familyRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsN membershipRoute subsetRoute
    comprehensionRoute familyRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed subsetUnary comprehensionUnary familyRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed familyUnary rowsH namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row familyRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧ Cont Q I subsetRead ∧
              Cont R E comprehensionRead ∧ Cont subsetRead comprehensionRead familyRead ∧
                Cont familyRead H namedRead ∧ PkgSig bundle P pkg)
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
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, familyRoute,
          namedRoute, packageRead⟩
  }
  exact ⟨cert, familyUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
