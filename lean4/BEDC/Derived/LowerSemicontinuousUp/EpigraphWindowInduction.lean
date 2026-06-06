import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphWindowInduction [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              Cont W R windowRead →
                Cont windowRead E epigraphRead →
                  Cont epigraphRead O locatedBoundary →
                    PkgSig bundle P pkg →
                      UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                        UnaryHistory locatedBoundary ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row locatedBoundary ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                                Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
                                  Cont epigraphRead O locatedBoundary)
                            (fun row : BHist => PkgSig bundle P pkg ∧ hsame row locatedBoundary)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro rootFields rowsW rowsR rowsE rowsO windowRoute epigraphRoute locatedRoute packageRead
  have _acceptedRootFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := rootFields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rowsW rowsR windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary rowsE epigraphRoute
  have locatedUnary : UnaryHistory locatedBoundary :=
    unary_cont_closed epigraphUnary rowsO locatedRoute
  have sourceAtBoundary : hsame locatedBoundary locatedBoundary ∧ UnaryHistory locatedBoundary :=
    ⟨hsame_refl locatedBoundary, locatedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row locatedBoundary ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
            Cont W R windowRead ∨ Cont windowRead E epigraphRead ∨
              Cont epigraphRead O locatedBoundary)
        (fun row : BHist => PkgSig bundle P pkg ∧ hsame row locatedBoundary)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedBoundary sourceAtBoundary
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr locatedRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨packageRead, source.left⟩
  }
  exact ⟨windowUnary, epigraphUnary, locatedUnary, cert⟩

end BEDC.Derived.LowerSemicontinuousUp
