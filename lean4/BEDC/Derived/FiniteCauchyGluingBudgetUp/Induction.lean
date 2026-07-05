import BEDC.Derived.FiniteCauchyGluingBudgetUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCauchyGluingBudgetCarrier_induction [AskSetup] [PackageSetup]
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
                                      hsame row T ∨ hsame row K ∨ hsame row D ∨
                                        hsame row R ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ Cont G L T ∧
                                        Cont T S K ∧ Cont K U D ∧ Cont D V R ∧
                                          Cont R N publicRead ∧
                                            PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory D ∧
                                    UnaryHistory R ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryG unaryL unaryS unaryU unaryV _unaryP unaryN _sameH gluingRoute
    synchronizerRoute streamRoute dyadicRoute publicRoute publicPkg
  have unaryT : UnaryHistory T :=
    unary_cont_closed unaryG unaryL gluingRoute
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryT unaryS synchronizerRoute
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
            hsame row T ∨ hsame row K ∨ hsame row D ∨ hsame row R ∨
              hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont G L T ∧ Cont T S K ∧ Cont K U D ∧
              Cont D V R ∧ Cont R N publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, gluingRoute, synchronizerRoute, streamRoute, dyadicRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, unaryT, unaryK, unaryD, unaryR, unaryPublic⟩

end BEDC.Derived.FiniteCauchyGluingBudgetUp
