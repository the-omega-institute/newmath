import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootRegularReadbackHandoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W → UnaryHistory R → UnaryHistory E → UnaryHistory O → UnaryHistory H →
        UnaryHistory C → Cont W R windowRead → Cont windowRead E epigraphRead →
          Cont epigraphRead O locatedRead → Cont locatedRead H transportRead →
            Cont transportRead C handoffRead → PkgSig bundle P pkg →
              PkgSig bundle N pkg → SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W R windowRead ∧
                    Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                      Cont locatedRead H transportRead ∧ Cont transportRead C handoffRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary cUnary windowRoute epigraphRoute
    locatedRoute transportRoute handoffRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed transportUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C handoffRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, transportRoute,
          handoffRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, windowUnary, epigraphUnary, locatedUnary, transportUnary, handoffUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
