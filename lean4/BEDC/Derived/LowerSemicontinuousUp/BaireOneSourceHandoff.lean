import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousBaireOneSourceHandoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N baireRead graphRead epigraphRead locatedRead transportRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory F ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory O ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    Cont F W baireRead ->
                      Cont baireRead R graphRead ->
                        Cont graphRead E epigraphRead ->
                          Cont epigraphRead O locatedRead ->
                            Cont locatedRead H transportRead ->
                              Cont transportRead C handoffRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row handoffRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row F ∨ hsame row W ∨ hsame row R ∨
                                            hsame row E ∨ hsame row O ∨ hsame row H ∨
                                              hsame row C ∨ hsame row handoffRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont F W baireRead ∧
                                            Cont baireRead R graphRead ∧
                                              Cont graphRead E epigraphRead ∧
                                                Cont epigraphRead O locatedRead ∧
                                                  Cont locatedRead H transportRead ∧
                                                    Cont transportRead C handoffRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                        hsame ∧ UnaryHistory baireRead ∧
                                      UnaryHistory graphRead ∧ UnaryHistory epigraphRead ∧
                                    UnaryHistory locatedRead ∧ UnaryHistory transportRead ∧
                                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields unaryF unaryW unaryR unaryE unaryO unaryH unaryC baireRoute graphRoute
    epigraphRoute locatedRoute transportRoute handoffRoute provenancePkg localNamePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed unaryF unaryW baireRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed baireUnary unaryR graphRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed graphUnary unaryE epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary unaryO locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary unaryH transportRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed transportUnary unaryC handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              hsame row H ∨ hsame row C ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F W baireRead ∧ Cont baireRead R graphRead ∧
              Cont graphRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                Cont locatedRead H transportRead ∧ Cont transportRead C handoffRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baireRoute, graphRoute, epigraphRoute, locatedRoute,
          transportRoute, handoffRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, baireUnary, graphUnary, epigraphUnary, locatedUnary, transportUnary,
      handoffUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
