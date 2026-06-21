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

theorem SetlikeMembershipClassifierPublicBoundary [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay subsetReplay comprehensionReplay extensionalReplay
      transportedReplay publicRead : BHist}
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
                          Cont subsetReplay comprehensionReplay extensionalReplay ->
                            Cont membershipReplay H transportedReplay ->
                              Cont transportedReplay C publicRead ->
                                PkgSig bundle P pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row publicRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                          hsame row R ∨ hsame row E ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row publicRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                          Cont Q I subsetReplay ∧
                                            Cont R E comprehensionReplay ∧
                                              Cont subsetReplay comprehensionReplay
                                                extensionalReplay ∧
                                                Cont membershipReplay H transportedReplay ∧
                                                  Cont transportedReplay C publicRead ∧
                                                    PkgSig bundle P pkg)
                                      hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsI rowsR rowsE rowsH rowsC membershipRoute subsetRoute
    comprehensionRoute extensionalRoute transportedRoute publicRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionReplay :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have _extensionalUnary : UnaryHistory extensionalReplay :=
    unary_cont_closed subsetUnary comprehensionUnary extensionalRoute
  have transportedUnary : UnaryHistory transportedReplay :=
    unary_cont_closed membershipUnary rowsH transportedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed transportedUnary rowsC publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ Cont Q I subsetReplay ∧
              Cont R E comprehensionReplay ∧
                Cont subsetReplay comprehensionReplay extensionalReplay ∧
                  Cont membershipReplay H transportedReplay ∧
                    Cont transportedReplay C publicRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          transportedRoute, publicRoute, packageRead⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SetlikeUp
