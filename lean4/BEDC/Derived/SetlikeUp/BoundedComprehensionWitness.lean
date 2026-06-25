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

theorem SetlikeBoundedComprehensionWitness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead boundedRead comprehensionRead transportRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont M Q membershipRead ->
                      Cont membershipRead I boundedRead ->
                        Cont boundedRead R comprehensionRead ->
                          Cont comprehensionRead H transportRead ->
                            Cont transportRead C replayRead ->
                              Cont replayRead N namedRead ->
                                PkgSig bundle P pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                          hsame row R ∨ hsame row membershipRead ∨
                                            hsame row boundedRead ∨
                                              hsame row comprehensionRead ∨
                                                hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M Q membershipRead ∧
                                          Cont membershipRead I boundedRead ∧
                                            Cont boundedRead R comprehensionRead ∧
                                              Cont comprehensionRead H transportRead ∧
                                                Cont transportRead C replayRead ∧
                                                  Cont replayRead N namedRead ∧
                                                    PkgSig bundle P pkg)
                                      hsame ∧
                                    UnaryHistory boundedRead ∧
                                      UnaryHistory comprehensionRead ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields mUnary qUnary iUnary rUnary hUnary cUnary nUnary membershipRoute boundedRoute
    comprehensionRoute transportRoute replayRoute namedRoute provenancePkg
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed mUnary qUnary membershipRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed membershipUnary iUnary boundedRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed boundedUnary rUnary comprehensionRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed comprehensionUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨
              hsame row membershipRead ∨ hsame row boundedRead ∨
                hsame row comprehensionRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧
              Cont membershipRead I boundedRead ∧ Cont boundedRead R comprehensionRead ∧
                Cont comprehensionRead H transportRead ∧ Cont transportRead C replayRead ∧
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
        ⟨source.right, membershipRoute, boundedRoute, comprehensionRoute, transportRoute,
          replayRoute, namedRoute, provenancePkg⟩
  }
  exact ⟨cert, boundedUnary, comprehensionUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
