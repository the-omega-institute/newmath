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

theorem SetlikeExtensionalityRootUnblock [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead extensionalRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory E ->
            UnaryHistory H ->
              Cont M Q membershipRead ->
                Cont membershipRead E extensionalRead ->
                  Cont extensionalRead H boundaryRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                              hsame row membershipRead ∨ hsame row extensionalRead ∨
                                hsame row boundaryRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M Q membershipRead ∧
                              Cont membershipRead E extensionalRead ∧
                                Cont extensionalRead H boundaryRead ∧ PkgSig bundle P pkg)
                          hsame ∧
                        UnaryHistory membershipRead ∧ UnaryHistory extensionalRead ∧
                          UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsE rowsH membershipRoute extensionalRoute boundaryRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed membershipUnary rowsE extensionalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed extensionalUnary rowsH boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
              hsame row membershipRead ∨ hsame row extensionalRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧
              Cont membershipRead E extensionalRead ∧ Cont extensionalRead H boundaryRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact ⟨source.right, membershipRoute, extensionalRoute, boundaryRoute, packageRead⟩
  }
  exact ⟨cert, membershipUnary, extensionalUnary, boundaryUnary⟩

theorem SetlikeRootExtensionalBoundary [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead comprehensionRead extensionalRead
      transportRead replayRead namedRead : BHist}
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
                        Cont M Q membershipRead ->
                          Cont Q I subsetRead ->
                            Cont R E comprehensionRead ->
                              Cont membershipRead subsetRead extensionalRead ->
                                Cont extensionalRead H transportRead ->
                                  Cont transportRead C replayRead ->
                                    Cont replayRead N namedRead ->
                                      PkgSig bundle P pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                                hsame row R ∨ hsame row E ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                    hsame row membershipRead ∨
                                                      hsame row subsetRead ∨
                                                        hsame row comprehensionRead ∨
                                                          hsame row extensionalRead ∨
                                                            hsame row transportRead ∨
                                                              hsame row replayRead ∨
                                                                hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont M Q membershipRead ∧
                                                Cont Q I subsetRead ∧ Cont R E comprehensionRead ∧
                                                  Cont membershipRead subsetRead
                                                    extensionalRead ∧
                                                    Cont extensionalRead H transportRead ∧
                                                      Cont transportRead C replayRead ∧
                                                        Cont replayRead N namedRead ∧
                                                          PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields mUnary qUnary iUnary rUnary eUnary hUnary cUnary _pUnary nUnary
    membershipRoute subsetRoute comprehensionRoute extensionalRoute transportRoute replayRoute
    namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed mUnary qUnary membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed qUnary iUnary subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed rUnary eUnary comprehensionRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed membershipUnary subsetUnary extensionalRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed extensionalUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row membershipRead ∨ hsame row subsetRead ∨
                  hsame row comprehensionRead ∨ hsame row extensionalRead ∨
                    hsame row transportRead ∨ hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧ Cont Q I subsetRead ∧
              Cont R E comprehensionRead ∧ Cont membershipRead subsetRead extensionalRead ∧
                Cont extensionalRead H transportRead ∧ Cont transportRead C replayRead ∧
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, comprehensionRoute, extensionalRoute,
          transportRoute, replayRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
