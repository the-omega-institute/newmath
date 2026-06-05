import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphCoverage [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              Cont W R windowRead ->
                Cont windowRead E epigraphRead ->
                  Cont epigraphRead O comparisonRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨
                                hsame row epigraphRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W R windowRead ∧
                                Cont windowRead E epigraphRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧ UnaryHistory windowRead ∧
                          UnaryHistory epigraphRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields windowUnary regularUnary epigraphUnary comparisonUnary windowRoute
    epigraphRoute comparisonRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary regularUnary windowRoute
  have epigraphReadUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowReadUnary epigraphUnary epigraphRoute
  have _comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed epigraphReadUnary comparisonUnary comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row epigraphRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro epigraphRead
        ⟨hsame_refl epigraphRead, epigraphReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, epigraphRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, windowReadUnary, epigraphReadUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
