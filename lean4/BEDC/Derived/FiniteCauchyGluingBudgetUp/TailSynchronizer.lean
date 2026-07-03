import BEDC.Derived.FiniteCauchyGluingBudgetUp.TasteGate

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCauchyGluingBudgetCarrier_tail_synchronizer [AskSetup] [PackageSetup]
    {G L S U V P N T K D R H publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory L ->
        UnaryHistory S ->
          UnaryHistory U ->
            UnaryHistory V ->
              UnaryHistory P ->
                UnaryHistory N ->
                  hsame H (append G L) ->
                    Cont G L T ->
                      Cont T S K ->
                        Cont K U D ->
                          Cont D V R ->
                            Cont R N publicRead ->
                              PkgSig bundle publicRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row S ∨ hsame row K ∨
                                        hsame row U ∨ hsame row D ∨ hsame row V ∨
                                          hsame row R ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ Cont T S K ∧
                                        Cont K U D ∧ Cont D V R ∧
                                          Cont R N publicRead ∧
                                            PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory D ∧
                                    UnaryHistory R ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryG unaryL unaryS unaryU unaryV _unaryP unaryN _sameH gluingLedger
    tailSynchronizer synchronizerStream streamDyadic realSeal publicPkg
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryG unaryL gluingLedger
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryT unaryS tailSynchronizer
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryK unaryU synchronizerStream
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryV streamDyadic
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryR unaryN realSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row K ∨ hsame row U ∨ hsame row D ∨
              hsame row V ∨ hsame row R ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont T S K ∧ Cont K U D ∧ Cont D V R ∧
              Cont R N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
        ⟨source.left, tailSynchronizer, synchronizerStream, streamDyadic, realSeal,
          publicPkg⟩
  }
  exact ⟨cert, unaryT, unaryK, unaryD, unaryR, unaryPublic⟩

theorem FiniteCauchyGluingBudgetCarrier_tail_stream_induction
    {T S K U D V R H _C P N publicRead : BHist} :
    UnaryHistory T ->
      UnaryHistory S ->
        UnaryHistory U ->
          UnaryHistory V ->
            UnaryHistory P ->
              UnaryHistory N ->
                hsame H (append T S) ->
                  Cont T S K ->
                    Cont K U D ->
                      Cont D V R ->
                        Cont R N publicRead ->
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row S ∨ hsame row K ∨ hsame row U ∨
                                  hsame row D ∨ hsame row V ∨ hsame row R ∨
                                    hsame row publicRead)
                              (fun row : BHist =>
                                hsame row publicRead ∧ Cont T S K ∧ Cont K U D ∧
                                  Cont D V R ∧ Cont R N publicRead)
                              hsame ∧
                            UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory R ∧
                              UnaryHistory publicRead ∧ hsame H (append T S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryT unaryS unaryU unaryV _unaryP unaryN sameH tailRoute streamRoute
    dyadicRoute publicRoute
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryT unaryS tailRoute
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryK unaryU streamRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryV dyadicRoute
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryR unaryN publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row K ∨ hsame row U ∨ hsame row D ∨
              hsame row V ∨ hsame row R ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont T S K ∧ Cont K U D ∧ Cont D V R ∧
              Cont R N publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublic⟩
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
      exact ⟨source.left, tailRoute, streamRoute, dyadicRoute, publicRoute⟩
  }
  exact ⟨cert, unaryK, unaryD, unaryR, unaryPublic, sameH⟩

end BEDC.Derived.FiniteCauchyGluingBudgetUp
