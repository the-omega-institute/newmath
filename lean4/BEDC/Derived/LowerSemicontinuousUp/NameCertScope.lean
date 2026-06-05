import BEDC.Derived.LowerSemicontinuousUp.RootRegularReadbackHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousNameCertScope [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                Cont X W scheduleRead ->
                  Cont scheduleRead R readbackRead ->
                    Cont readbackRead E epigraphRead ->
                      Cont epigraphRead N scopeRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row W ∨ hsame row R ∨
                                    hsame row E ∨ hsame row P ∨ hsame row N ∨
                                      hsame row scheduleRead ∨ hsame row readbackRead ∨
                                        hsame row epigraphRead ∨ hsame row scopeRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X W scheduleRead ∧
                                    Cont scheduleRead R readbackRead ∧
                                      Cont readbackRead E epigraphRead ∧
                                        Cont epigraphRead N scopeRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory epigraphRead ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fields xUnary wUnary rUnary eUnary nUnary scheduleRoute readbackRoute epigraphRoute
    scopeRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed xUnary wUnary scheduleRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed epigraphUnary nUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row P ∨
              hsame row N ∨ hsame row scheduleRead ∨ hsame row readbackRead ∨
                hsame row epigraphRead ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧ Cont scheduleRead R readbackRead ∧
              Cont readbackRead E epigraphRead ∧ Cont epigraphRead N scopeRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, epigraphRoute, scopeRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, epigraphUnary, scopeUnary⟩

theorem LowerSemicontinuousKernelSourceNameCertScope_handoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                Cont X W scheduleRead ->
                  Cont scheduleRead R readbackRead ->
                    Cont readbackRead E epigraphRead ->
                      Cont epigraphRead N scopeRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            (SemanticNameCert
                                (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row F ∨ hsame row E ∨
                                    hsame row W ∨ hsame row R ∨ hsame row O ∨
                                      hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row scheduleRead ∨
                                          hsame row readbackRead ∨ hsame row epigraphRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X W scheduleRead ∧
                                    Cont scheduleRead R readbackRead ∧
                                      Cont readbackRead E epigraphRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory epigraphRead) ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row W ∨ hsame row R ∨
                                    hsame row E ∨ hsame row P ∨ hsame row N ∨
                                      hsame row scheduleRead ∨ hsame row readbackRead ∨
                                        hsame row epigraphRead ∨ hsame row scopeRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X W scheduleRead ∧
                                    Cont scheduleRead R readbackRead ∧
                                      Cont readbackRead E epigraphRead ∧
                                        Cont epigraphRead N scopeRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory epigraphRead ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fields xUnary wUnary rUnary eUnary nUnary scheduleRoute readbackRoute epigraphRoute
    scopeRoute provenancePkg namePkg
  have kernelSource :
      SemanticNameCert
          (fun row : BHist => hsame row epigraphRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
              hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row scheduleRead ∨
                  hsame row readbackRead ∨ hsame row epigraphRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧
              Cont scheduleRead R readbackRead ∧ Cont readbackRead E epigraphRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧ UnaryHistory epigraphRead :=
    LowerSemicontinuousKernelSource_obligations xUnary wUnary rUnary eUnary scheduleRoute
      readbackRoute epigraphRoute provenancePkg namePkg
  have scopeCert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row P ∨
              hsame row N ∨ hsame row scheduleRead ∨ hsame row readbackRead ∨
                hsame row epigraphRead ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧ Cont scheduleRead R readbackRead ∧
              Cont readbackRead E epigraphRead ∧ Cont epigraphRead N scopeRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
          UnaryHistory epigraphRead ∧ UnaryHistory scopeRead :=
    LowerSemicontinuousNameCertScope fields xUnary wUnary rUnary eUnary nUnary scheduleRoute
      readbackRoute epigraphRoute scopeRoute provenancePkg namePkg
  exact ⟨kernelSource, scopeCert⟩

end BEDC.Derived.LowerSemicontinuousUp
