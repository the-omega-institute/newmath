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

theorem SetlikeMembershipRoute [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont M Q membershipReplay ->
                  Cont Q I subsetReplay ->
                    Cont R E comprehensionReplay ->
                      Cont membershipReplay subsetReplay extensionalReplay ->
                        Cont extensionalReplay comprehensionReplay routeRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                      hsame row R ∨ hsame row E ∨
                                        hsame row membershipReplay ∨
                                          hsame row subsetReplay ∨
                                            hsame row comprehensionReplay ∨
                                              hsame row routeRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                      Cont Q I subsetReplay ∧ Cont R E comprehensionReplay ∧
                                        Cont membershipReplay subsetReplay extensionalReplay ∧
                                          Cont extensionalReplay comprehensionReplay routeRead ∧
                                            PkgSig bundle P pkg)
                                  hsame ∧
                              UnaryHistory membershipReplay ∧ UnaryHistory subsetReplay ∧
                                UnaryHistory comprehensionReplay ∧ UnaryHistory extensionalReplay ∧
                                  UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE membershipRoute subsetRoute comprehensionRoute
    extensionalRoute routePkg routePackage
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
    unary_cont_closed extensionalUnary comprehensionUnary routePkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row membershipReplay ∨ hsame row subsetReplay ∨
                hsame row comprehensionReplay ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ Cont Q I subsetReplay ∧
              Cont R E comprehensionReplay ∧
                Cont membershipReplay subsetReplay extensionalReplay ∧
                  Cont extensionalReplay comprehensionReplay routeRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          routePkg, routePackage⟩
  }
  exact
    ⟨cert, membershipUnary, subsetUnary, comprehensionUnary, extensionalUnary, routeUnary⟩

end BEDC.Derived.SetlikeUp
