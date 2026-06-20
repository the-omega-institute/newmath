import BEDC.Derived.SetlikeUp.MembershipRoute

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeRootMembershipTransport [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    Cont M Q membershipReplay ->
                      Cont Q I subsetReplay ->
                        Cont R E comprehensionReplay ->
                          Cont membershipReplay subsetReplay extensionalReplay ->
                            Cont extensionalReplay comprehensionReplay routeRead ->
                              Cont routeRead H transportRead ->
                                PkgSig bundle P pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row transportRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                          hsame row R ∨ hsame row E ∨ hsame row routeRead ∨
                                            hsame row transportRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont extensionalReplay comprehensionReplay routeRead ∧
                                            Cont routeRead H transportRead ∧
                                              PkgSig bundle P pkg)
                                      hsame ∧ UnaryHistory routeRead ∧
                                    UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH _rowsC membershipRoute subsetRoute
    comprehensionRoute extensionalRoute routeCont transportCont routePackage
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
    unary_cont_closed extensionalUnary comprehensionUnary routeCont
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed routeUnary rowsH transportCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row routeRead ∨ hsame row transportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont extensionalReplay comprehensionReplay routeRead ∧
              Cont routeRead H transportRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportRead ⟨hsame_refl transportRead, transportUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeCont, transportCont, routePackage⟩
  }
  exact ⟨cert, routeUnary, transportUnary⟩

end BEDC.Derived.SetlikeUp
