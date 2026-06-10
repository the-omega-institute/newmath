import BEDC.Derived.FirstExitChannelUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FirstExitChannelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FirstExitChannelNamecertObligations [AskSetup] [PackageSetup]
    {O B T K L H C P N exitRead transportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    firstExitChannelFields (FirstExitChannelUp.mk O B T K L H C P N) =
        [O, B, T, K, L, H, C, P, N] ->
      UnaryHistory O -> UnaryHistory B -> UnaryHistory T -> UnaryHistory K -> UnaryHistory L ->
        UnaryHistory H -> UnaryHistory C ->
          Cont O B exitRead -> Cont exitRead L transportRead -> Cont transportRead C replayRead ->
            PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row replayRead /\ UnaryHistory row)
                (fun row : BHist =>
                  hsame row O \/ hsame row B \/ hsame row T \/ hsame row K \/ hsame row L \/
                    hsame row H \/ hsame row C \/ hsame row P \/ hsame row N \/
                      hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row /\ Cont O B exitRead /\ Cont exitRead L transportRead /\
                    Cont transportRead C replayRead /\ PkgSig bundle P pkg /\
                      PkgSig bundle N pkg)
                hsame /\ UnaryHistory exitRead /\ UnaryHistory transportRead /\
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields oUnary bUnary _tUnary _kUnary lUnary _hUnary cUnary exitRoute transportRoute
    replayRoute provenancePkg namePkg
  have _acceptedFields :
      firstExitChannelFields (FirstExitChannelUp.mk O B T K L H C P N) =
        [O, B, T, K, L, H, C, P, N] := fields
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed oUnary bUnary exitRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed exitUnary lUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row replayRead /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row O \/ hsame row B \/ hsame row T \/ hsame row K \/ hsame row L \/
            hsame row H \/ hsame row C \/ hsame row P \/ hsame row N \/
              hsame row replayRead)
        (fun row : BHist =>
          UnaryHistory row /\ Cont O B exitRead /\ Cont exitRead L transportRead /\
            Cont transportRead C replayRead /\ PkgSig bundle P pkg /\ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exitRoute, transportRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, exitUnary, transportUnary, replayUnary⟩

end BEDC.Derived.FirstExitChannelUp
