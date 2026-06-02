import BEDC.Derived.LowerSemicontinuousUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def lowerSemicontinuousRootFields : LowerSemicontinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerSemicontinuousUp.mk X F E W R O H C P N => [X, F, E, W, R, O, H, C, P, N]

theorem LowerSemicontinuousReal_handoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              Cont W R windowRead ->
                Cont windowRead E epigraphRead ->
                  Cont epigraphRead O realSeal ->
                    PkgSig bundle P pkg ->
                      UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                        UnaryHistory realSeal ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                                Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
                                  Cont epigraphRead O realSeal)
                            (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields rowsW rowsR rowsE rowsO windowRoute epigraphRoute realSealRoute packageRead
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rowsW rowsR windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary rowsE epigraphRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed epigraphUnary rowsO realSealRoute
  have sourceAtSeal : hsame realSeal realSeal ∧ UnaryHistory realSeal :=
    ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
            Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
              Cont epigraphRead O realSeal)
        (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realSealRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨packageRead, source.left⟩
  }
  exact ⟨windowUnary, epigraphUnary, realSealUnary, cert⟩

end BEDC.Derived.LowerSemicontinuousUp
