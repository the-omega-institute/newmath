import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphSiblingRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N epigraphRead siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory epigraphRead →
        UnaryHistory P →
          Cont epigraphRead P siblingRead →
            PkgSig bundle P pkg →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row epigraphRead ∨ hsame row siblingRead ∨
                        Cont epigraphRead P siblingRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont epigraphRead P siblingRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields epigraphUnary pUnary siblingRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed epigraphUnary pUnary siblingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epigraphRead ∨ hsame row siblingRead ∨ Cont epigraphRead P siblingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epigraphRead P siblingRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro siblingRead ⟨hsame_refl siblingRead, siblingUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inl sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, siblingRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, siblingUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
