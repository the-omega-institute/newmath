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

theorem SetlikeRootMembershipTripleUnblock [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay firstOrderRead modelRead typeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory P ->
                Cont M Q membershipReplay ->
                  Cont membershipReplay H firstOrderRead ->
                    Cont membershipReplay C modelRead ->
                      Cont membershipReplay P typeRead ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row firstOrderRead ∨ hsame row modelRead ∨
                                  hsame row typeRead)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
                                  hsame row firstOrderRead ∨ hsame row modelRead ∨
                                    hsame row typeRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M Q membershipReplay ∧
                                  PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory membershipReplay ∧ UnaryHistory firstOrderRead ∧
                              UnaryHistory modelRead ∧ UnaryHistory typeRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC rowsP membershipRoute firstOrderRoute modelRoute
    typeRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have firstOrderUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed membershipUnary rowsH firstOrderRoute
  have modelUnary : UnaryHistory modelRead :=
    unary_cont_closed membershipUnary rowsC modelRoute
  have typeUnary : UnaryHistory typeRead :=
    unary_cont_closed membershipUnary rowsP typeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row typeRead)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
              hsame row firstOrderRead ∨ hsame row modelRead ∨ hsame row typeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro firstOrderRead (Or.inl (hsame_refl firstOrderRead))
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
        intro row other sameRows source
        cases source with
        | inl firstSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) firstSource)
        | inr tail =>
            cases tail with
            | inl modelSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) modelSource))
            | inr typeSource =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) typeSource))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl firstSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inl firstSource)))
      | inr tail =>
          cases tail with
          | inl modelSource =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl modelSource))))
          | inr typeSource =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr typeSource))))
    ledger_sound := by
      intro row source
      cases source with
      | inl firstSource =>
          exact
            ⟨unary_transport firstOrderUnary (hsame_symm firstSource), membershipRoute,
              packageRead⟩
      | inr tail =>
          cases tail with
          | inl modelSource =>
              exact
                ⟨unary_transport modelUnary (hsame_symm modelSource), membershipRoute,
                  packageRead⟩
          | inr typeSource =>
              exact
                ⟨unary_transport typeUnary (hsame_symm typeSource), membershipRoute,
                  packageRead⟩
  }
  exact ⟨cert, membershipUnary, firstOrderUnary, modelUnary, typeUnary⟩

end BEDC.Derived.SetlikeUp
