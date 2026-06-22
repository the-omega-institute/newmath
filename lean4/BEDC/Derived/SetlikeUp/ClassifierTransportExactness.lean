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

theorem SetlikeClassifierTransportExactness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N subsetRead comprehensionRead extensionalRead transportedClassifier
      replayedClassifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory I ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  Cont Q I subsetRead ->
                    Cont R E comprehensionRead ->
                      Cont subsetRead comprehensionRead extensionalRead ->
                        Cont Q H transportedClassifier ->
                          Cont transportedClassifier C replayedClassifier ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row replayedClassifier ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row Q ∨ hsame row I ∨ hsame row R ∨
                                      hsame row E ∨ hsame row H ∨ hsame row C ∨
                                        hsame row subsetRead ∨
                                          hsame row comprehensionRead ∨
                                            hsame row extensionalRead ∨
                                              hsame row transportedClassifier ∨
                                                hsame row replayedClassifier)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont Q I subsetRead ∧
                                      Cont R E comprehensionRead ∧
                                        Cont subsetRead comprehensionRead extensionalRead ∧
                                          Cont Q H transportedClassifier ∧
                                            Cont transportedClassifier C replayedClassifier ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory replayedClassifier := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsQ rowsI rowsR rowsE rowsH rowsC subsetRoute comprehensionRoute
    extensionalRoute transportedRoute replayedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed rowsR rowsE comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed subsetUnary comprehensionUnary extensionalRoute
  have transportedUnary : UnaryHistory transportedClassifier :=
    unary_cont_closed rowsQ rowsH transportedRoute
  have replayedUnary : UnaryHistory replayedClassifier :=
    unary_cont_closed transportedUnary rowsC replayedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayedClassifier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row subsetRead ∨ hsame row comprehensionRead ∨
                hsame row extensionalRead ∨ hsame row transportedClassifier ∨
                  hsame row replayedClassifier)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q I subsetRead ∧ Cont R E comprehensionRead ∧
              Cont subsetRead comprehensionRead extensionalRead ∧
                Cont Q H transportedClassifier ∧
                  Cont transportedClassifier C replayedClassifier ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayedClassifier
        ⟨hsame_refl replayedClassifier, replayedUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, subsetRoute, comprehensionRoute, extensionalRoute, transportedRoute,
          replayedRoute, packageRead⟩
  }
  exact ⟨cert, replayedUnary⟩

end BEDC.Derived.SetlikeUp
