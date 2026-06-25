import BEDC.Derived.FinitePrefixAutomatonUp.Determinacy
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_deterministic_readback
    {Q q0 A T W R R' E E' H C P N acceptance acceptance' : BHist} :
    UnaryHistory q0 ->
      UnaryHistory W ->
        UnaryHistory H ->
          UnaryHistory A ->
            Cont q0 W R ->
              Cont q0 W R' ->
                Cont R H E ->
                  Cont R' H E' ->
                    Cont E A acceptance ->
                      Cont E' A acceptance' ->
                        hsame R R' ∧ hsame E E' ∧ hsame acceptance acceptance' ∧
                          UnaryHistory E ∧ UnaryHistory E' ∧ UnaryHistory acceptance ∧
                            UnaryHistory acceptance' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro q0Unary wUnary hUnary acceptingUnary runRoute runRoute' endpointRoute endpointRoute'
    acceptanceRoute acceptanceRoute'
  have runPack :
      hsame R R' ∧ UnaryHistory R ∧ UnaryHistory R' ∧ UnaryHistory E ∧
        UnaryHistory E' :=
    FinitePrefixAutomatonCarrier_prefix_run_determinacy q0Unary wUnary hUnary runRoute
      runRoute' endpointRoute endpointRoute'
  have sameEndpoint : hsame E E' :=
    cont_respects_hsame runPack.left (hsame_refl H) endpointRoute endpointRoute'
  have sameAcceptance : hsame acceptance acceptance' :=
    cont_respects_hsame sameEndpoint (hsame_refl A) acceptanceRoute acceptanceRoute'
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed runPack.right.right.right.left acceptingUnary acceptanceRoute
  have acceptanceUnary' : UnaryHistory acceptance' :=
    unary_cont_closed runPack.right.right.right.right acceptingUnary acceptanceRoute'
  exact
    ⟨runPack.left, sameEndpoint, sameAcceptance, runPack.right.right.right.left,
      runPack.right.right.right.right, acceptanceUnary, acceptanceUnary'⟩

theorem FinitePrefixAutomatonDeterministicReadback [AskSetup] [PackageSetup]
    (F : FinitePrefixAutomatonUp)
    {Q q0 A T W R E H C P N runRead endpointRead acceptanceRead : BHist} :
    finitePrefixAutomatonFields F = [Q, q0, A, T, W, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory q0 ->
          UnaryHistory T ->
            UnaryHistory W ->
              UnaryHistory A ->
                Cont q0 W runRead ->
                  Cont runRead T endpointRead ->
                    Cont endpointRead A acceptanceRead ->
                      SemanticNameCert
                          (fun row : BHist => hsame row acceptanceRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row q0 ∨ hsame row T ∨ hsame row W ∨
                              hsame row R ∨ hsame row E ∨ hsame row acceptanceRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont q0 W runRead ∧
                              Cont runRead T endpointRead ∧
                                Cont endpointRead A acceptanceRead)
                          hsame ∧
                        UnaryHistory runRead ∧ UnaryHistory endpointRead ∧
                          UnaryHistory acceptanceRead := by
  -- BEDC touchpoint anchor: FinitePrefixAutomatonUp finitePrefixAutomatonFields BHist Cont SemanticNameCert hsame UnaryHistory
  intro fields _qUnary q0Unary tUnary wUnary aUnary runRoute endpointRoute acceptanceRoute
  have _acceptedFields :
      finitePrefixAutomatonFields F = [Q, q0, A, T, W, R, E, H, C, P, N] := fields
  have runUnary : UnaryHistory runRead :=
    unary_cont_closed q0Unary wUnary runRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed runUnary tUnary endpointRoute
  have acceptanceUnary : UnaryHistory acceptanceRead :=
    unary_cont_closed endpointUnary aUnary acceptanceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row acceptanceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row q0 ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row acceptanceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q0 W runRead ∧ Cont runRead T endpointRead ∧
              Cont endpointRead A acceptanceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptanceRead ⟨hsame_refl acceptanceRead,
        acceptanceUnary⟩
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
      exact ⟨source.right, runRoute, endpointRoute, acceptanceRoute⟩
  }
  exact ⟨cert, runUnary, endpointUnary, acceptanceUnary⟩

end BEDC.Derived.FinitePrefixAutomatonUp
