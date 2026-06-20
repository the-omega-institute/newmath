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

theorem SetlikeRootMembershipObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay transportedReplay continuedReplay
      provenanceReplay namedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont M Q membershipReplay ->
                    Cont membershipReplay H transportedReplay ->
                      Cont transportedReplay C continuedReplay ->
                        Cont continuedReplay P provenanceReplay ->
                          Cont provenanceReplay N namedReplay ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row membershipReplay ∨
                                          hsame row transportedReplay ∨
                                            hsame row continuedReplay ∨
                                              hsame row provenanceReplay ∨
                                                hsame row namedReplay)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                      Cont membershipReplay H transportedReplay ∧
                                        Cont transportedReplay C continuedReplay ∧
                                          Cont continuedReplay P provenanceReplay ∧
                                            Cont provenanceReplay N namedReplay ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory membershipReplay ∧
                                  UnaryHistory transportedReplay ∧
                                    UnaryHistory continuedReplay ∧
                                      UnaryHistory provenanceReplay ∧
                                        UnaryHistory namedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP rowsN membershipRoute transportedRoute
    continuedRoute provenanceRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have transportedUnary : UnaryHistory transportedReplay :=
    unary_cont_closed membershipUnary rowsH transportedRoute
  have continuedUnary : UnaryHistory continuedReplay :=
    unary_cont_closed transportedUnary rowsC continuedRoute
  have provenanceUnary : UnaryHistory provenanceReplay :=
    unary_cont_closed continuedUnary rowsP provenanceRoute
  have namedUnary : UnaryHistory namedReplay :=
    unary_cont_closed provenanceUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row membershipReplay ∨ hsame row transportedReplay ∨
                hsame row continuedReplay ∨ hsame row provenanceReplay ∨
                  hsame row namedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧
              Cont membershipReplay H transportedReplay ∧
                Cont transportedReplay C continuedReplay ∧
                  Cont continuedReplay P provenanceReplay ∧
                    Cont provenanceReplay N namedReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedReplay ⟨hsame_refl namedReplay, namedUnary⟩
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
        ⟨source.right, membershipRoute, transportedRoute, continuedRoute, provenanceRoute,
          namedRoute, packageRead⟩
  }
  exact
    ⟨cert, membershipUnary, transportedUnary, continuedUnary, provenanceUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
