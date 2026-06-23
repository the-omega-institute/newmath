import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonPublicObligationCertificate [AskSetup] [PackageSetup]
    (F : FinitePrefixAutomatonUp)
    {Q q0 A T W R E H C P N transitionRead endpointRead acceptanceRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finitePrefixAutomatonFields F = [Q, q0, A, T, W, R, E, H, C, P, N] →
      UnaryHistory Q →
        UnaryHistory q0 →
          UnaryHistory A →
            UnaryHistory T →
              UnaryHistory W →
                UnaryHistory R →
                  UnaryHistory E →
                    UnaryHistory H →
                      UnaryHistory C →
                        UnaryHistory N →
                          Cont q0 W transitionRead →
                            Cont transitionRead T endpointRead →
                              Cont endpointRead R acceptanceRead →
                                Cont acceptanceRead H transportRead →
                                  Cont transportRead C replayRead →
                                    Cont replayRead N namedRead →
                                      PkgSig bundle P pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row Q ∨ hsame row q0 ∨
                                                hsame row A ∨ hsame row T ∨
                                                  hsame row W ∨ hsame row R ∨
                                                    hsame row E ∨ hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont q0 W transitionRead ∧
                                                  Cont transitionRead T endpointRead ∧
                                                    Cont endpointRead R acceptanceRead ∧
                                                      Cont acceptanceRead H transportRead ∧
                                                        Cont transportRead C replayRead ∧
                                                          Cont replayRead N namedRead ∧
                                                            PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FinitePrefixAutomatonUp finitePrefixAutomatonFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields qUnary q0Unary aUnary tUnary wUnary rUnary _eUnary hUnary cUnary nUnary
    transitionRoute endpointRoute acceptanceRoute transportRoute replayRoute namedRoute
    packageRead
  have _acceptedFields :
      finitePrefixAutomatonFields F = [Q, q0, A, T, W, R, E, H, C, P, N] := fields
  have transitionUnary : UnaryHistory transitionRead :=
    unary_cont_closed q0Unary wUnary transitionRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed transitionUnary tUnary endpointRoute
  have acceptanceUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed endpointUnary rUnary acceptanceRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed acceptanceUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row q0 ∨ hsame row A ∨ hsame row T ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q0 W transitionRead ∧
              Cont transitionRead T endpointRead ∧ Cont endpointRead R acceptanceRead ∧
                Cont acceptanceRead H transportRead ∧ Cont transportRead C replayRead ∧
                  Cont replayRead N namedRead ∧ PkgSig bundle P pkg)
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
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, transitionRoute, endpointRoute, acceptanceRoute, transportRoute,
          replayRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.FinitePrefixAutomatonUp
