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

theorem SetlikeRootClassifierTransport [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay transportedReplay continuedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              Cont M Q membershipReplay ->
                Cont membershipReplay H transportedReplay ->
                  Cont transportedReplay C continuedReplay ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row continuedReplay ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨
                              hsame row H ∨ hsame row transportedReplay ∨ hsame row C ∨
                                hsame row continuedReplay)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M Q membershipReplay ∧
                              Cont membershipReplay H transportedReplay ∧
                                Cont transportedReplay C continuedReplay ∧
                                  PkgSig bundle P pkg)
                          hsame ∧ UnaryHistory membershipReplay ∧
                        UnaryHistory transportedReplay ∧ UnaryHistory continuedReplay := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro fields rowsM rowsQ rowsH rowsC membershipRoute transportedRoute continuedRoute
    routePackage
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ membershipRoute
  have transportedUnary : UnaryHistory transportedReplay :=
    unary_cont_closed membershipUnary rowsH transportedRoute
  have continuedUnary : UnaryHistory continuedReplay :=
    unary_cont_closed transportedUnary rowsC continuedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row continuedReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row membershipReplay ∨ hsame row H ∨
              hsame row transportedReplay ∨ hsame row C ∨ hsame row continuedReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipReplay ∧
              Cont membershipReplay H transportedReplay ∧
                Cont transportedReplay C continuedReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro continuedReplay
        ⟨hsame_refl continuedReplay, continuedUnary⟩
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
      exact ⟨source.right, membershipRoute, transportedRoute, continuedRoute, routePackage⟩
  }
  exact ⟨cert, membershipUnary, transportedUnary, continuedUnary⟩

end BEDC.Derived.SetlikeUp
