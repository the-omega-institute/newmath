import BEDC.Derived.SetlikeUp.RootNameCertObligations

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeClassifierTransportRoute [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N subsetRead comprehensionRead boundaryRead transportRead replayRead
      provenanceRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory I ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont Q I subsetRead ->
                        Cont subsetRead R comprehensionRead ->
                          Cont comprehensionRead E boundaryRead ->
                            Cont boundaryRead H transportRead ->
                              Cont transportRead C replayRead ->
                                Cont replayRead P provenanceRead ->
                                  Cont provenanceRead N namedRead ->
                                    PkgSig bundle P pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row Q ∨ hsame row I ∨ hsame row R ∨
                                              hsame row E ∨ hsame row H ∨ hsame row C ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row subsetRead ∨
                                                    hsame row comprehensionRead ∨
                                                      hsame row boundaryRead ∨
                                                        hsame row transportRead ∨
                                                          hsame row replayRead ∨
                                                            hsame row provenanceRead ∨
                                                              hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont Q I subsetRead ∧
                                              Cont subsetRead R comprehensionRead ∧
                                                Cont comprehensionRead E boundaryRead ∧
                                                  Cont boundaryRead H transportRead ∧
                                                    Cont transportRead C replayRead ∧
                                                      Cont replayRead P provenanceRead ∧
                                                        Cont provenanceRead N namedRead ∧
                                                          PkgSig bundle P pkg)
                                          hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsQ rowsI rowsR rowsE rowsH rowsC rowsP rowsN subsetRoute
    comprehensionRoute boundaryRoute transportRoute replayRoute provenanceRoute namedRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed subsetUnary rowsR comprehensionRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed comprehensionUnary rowsE boundaryRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed boundaryUnary rowsH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary rowsC replayRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayUnary rowsP provenanceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row subsetRead ∨
                hsame row comprehensionRead ∨ hsame row boundaryRead ∨
                  hsame row transportRead ∨ hsame row replayRead ∨
                    hsame row provenanceRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q I subsetRead ∧
              Cont subsetRead R comprehensionRead ∧ Cont comprehensionRead E boundaryRead ∧
                Cont boundaryRead H transportRead ∧ Cont transportRead C replayRead ∧
                  Cont replayRead P provenanceRead ∧ Cont provenanceRead N namedRead ∧
                    PkgSig bundle P pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, subsetRoute, comprehensionRoute, boundaryRoute, transportRoute,
          replayRoute, provenanceRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
