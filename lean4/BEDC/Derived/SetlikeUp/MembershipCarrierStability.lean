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

theorem SetlikeMembershipCarrierStability [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont M Q membershipRead ->
                    Cont membershipRead H transportRead ->
                      Cont transportRead C replayRead ->
                        Cont replayRead P namedRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row Q ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row membershipRead ∨
                                        hsame row transportRead ∨ hsame row replayRead ∨
                                          hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont M Q membershipRead ∧
                                    Cont membershipRead H transportRead ∧
                                      Cont transportRead C replayRead ∧
                                        Cont replayRead P namedRead ∧ PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP _rowsN membershipRoute transportRoute replayRoute
    namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed membershipUnary rowsH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary rowsC replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary rowsP namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row membershipRead ∨ hsame row transportRead ∨
                hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧
              Cont membershipRead H transportRead ∧ Cont transportRead C replayRead ∧
                Cont replayRead P namedRead ∧ PkgSig bundle P pkg)
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
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, transportRoute, replayRoute, namedRoute,
          packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
