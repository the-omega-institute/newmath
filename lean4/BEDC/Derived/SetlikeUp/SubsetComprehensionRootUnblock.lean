import BEDC.Derived.SetlikeUp.RootSubsetLedgerNonescape

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeSubsetComprehensionRootUnblock [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay boundaryReplay
      namedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory N ->
                  Cont M Q membershipReplay ->
                    Cont membershipReplay I subsetReplay ->
                      Cont subsetReplay R comprehensionReplay ->
                        Cont comprehensionReplay E boundaryReplay ->
                          Cont boundaryReplay N namedReplay ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row namedReplay ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                      hsame row R ∨ hsame row E ∨
                                        hsame row subsetReplay ∨
                                          hsame row comprehensionReplay ∨
                                            hsame row boundaryReplay ∨
                                              hsame row namedReplay)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                      Cont membershipReplay I subsetReplay ∧
                                        Cont subsetReplay R comprehensionReplay ∧
                                          Cont comprehensionReplay E boundaryReplay ∧
                                            Cont boundaryReplay N namedReplay ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory subsetReplay ∧
                                  UnaryHistory comprehensionReplay ∧
                                    UnaryHistory boundaryReplay ∧
                                      UnaryHistory namedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsN membershipRoute subsetRoute
    comprehensionRoute boundaryRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed membershipUnary rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed subsetUnary rowsR comprehensionRoute
  have boundaryUnary : UnaryHistory boundaryReplay :=
    unary_cont_closed comprehensionUnary rowsE boundaryRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed boundaryUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row subsetReplay ∨ hsame row comprehensionReplay ∨
                hsame row boundaryReplay ∨ hsame row namedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧
              Cont membershipReplay I subsetReplay ∧
                Cont subsetReplay R comprehensionReplay ∧
                  Cont comprehensionReplay E boundaryReplay ∧ Cont boundaryReplay N namedReplay ∧
                    PkgSig bundle P pkg)
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
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, boundaryRoute,
          namedRoute, packageRead⟩
  }
  exact ⟨cert, subsetUnary, comprehensionUnary, boundaryUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
