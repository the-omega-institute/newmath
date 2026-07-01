import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphDependencyRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead realSeal seriesRead
      epigraphConsumer dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory N →
                UnaryHistory P →
                  Cont W R windowRead →
                    Cont windowRead E epigraphRead →
                      Cont epigraphRead O locatedRead →
                        Cont locatedRead N realSeal →
                          Cont realSeal P seriesRead →
                            Cont epigraphRead seriesRead dependencyRead →
                            Cont E O epigraphConsumer →
                              Cont epigraphConsumer N dependencyRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    PkgSig bundle dependencyRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row dependencyRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row W ∨ hsame row R ∨ hsame row E ∨
                                              hsame row O ∨ hsame row N ∨ hsame row P ∨
                                                hsame row seriesRead ∨
                                                  Cont epigraphRead seriesRead dependencyRead ∨
                                                    Cont epigraphConsumer N dependencyRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont W R windowRead ∧
                                              Cont windowRead E epigraphRead ∧
                                                Cont epigraphRead O locatedRead ∧
                                                  Cont locatedRead N realSeal ∧
                                                    Cont realSeal P seriesRead ∧
                                                      Cont E O epigraphConsumer ∧
                                                        Cont epigraphRead seriesRead
                                                          dependencyRead ∧
                                                          Cont epigraphConsumer N
                                                            dependencyRead ∧
                                                            PkgSig bundle dependencyRead pkg)
                                          hsame ∧
                                        UnaryHistory seriesRead ∧
                                          UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: LowerSemicontinuousUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields wUnary rUnary eUnary oUnary nUnary pUnary windowRoute epigraphRoute
    locatedRoute realSealRoute seriesRoute directDependencyRoute epigraphConsumerRoute
    consumerDependencyRoute _pPkg _nPkg dependencyPkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed locatedUnary nUnary realSealRoute
  have seriesUnary : UnaryHistory seriesRead :=
    unary_cont_closed realSealUnary pUnary seriesRoute
  have epigraphConsumerUnary : UnaryHistory epigraphConsumer :=
    unary_cont_closed eUnary oUnary epigraphConsumerRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed epigraphConsumerUnary nUnary consumerDependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row N ∨
              hsame row P ∨ hsame row seriesRead ∨
                Cont epigraphRead seriesRead dependencyRead ∨
                  Cont epigraphConsumer N dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead N realSeal ∧
                Cont realSeal P seriesRead ∧ Cont E O epigraphConsumer ∧
                  Cont epigraphRead seriesRead dependencyRead ∧
                    Cont epigraphConsumer N dependencyRead ∧ PkgSig bundle dependencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead ⟨hsame_refl dependencyRead, dependencyUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      left
      exact directDependencyRoute
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, realSealRoute, seriesRoute,
          epigraphConsumerRoute, directDependencyRoute, consumerDependencyRoute, dependencyPkg⟩
  }
  exact ⟨cert, seriesUnary, dependencyUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
