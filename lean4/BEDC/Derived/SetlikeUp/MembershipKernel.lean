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

theorem SetlikeMembershipKernel_obligations [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipReplay : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          Cont M Q membershipReplay ->
            PkgSig bundle P pkg ->
              UnaryHistory membershipReplay ∧
                SemanticNameCert
                  (fun row : BHist => hsame row membershipReplay ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ Cont M Q membershipReplay)
                  (fun row : BHist => PkgSig bundle P pkg ∧ hsame row membershipReplay)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields rowsM rowsQ replayRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have replayUnary : UnaryHistory membershipReplay :=
    unary_cont_closed rowsM rowsQ replayRoute
  have sourceAtReplay : hsame membershipReplay membershipReplay ∧ UnaryHistory membershipReplay :=
    ⟨hsame_refl membershipReplay, replayUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row membershipReplay ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
            hsame row P ∨ hsame row N ∨ Cont M Q membershipReplay)
        (fun row : BHist => PkgSig bundle P pkg ∧ hsame row membershipReplay)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro membershipReplay sourceAtReplay
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr replayRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨packageRead, source.left⟩
  }
  exact ⟨replayUnary, cert⟩

end BEDC.Derived.SetlikeUp
