import BEDC.Derived.CalculusUp.RootRealSealNonescape
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusContinuousMapGraphReplayObligation [AskSetup] [PackageSetup]
    {R L C D I Q H T P N graphRead limitRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory L ->
        UnaryHistory C ->
          UnaryHistory Q ->
            UnaryHistory H ->
              UnaryHistory T ->
                Cont R L limitRead ->
                  Cont limitRead C graphRead ->
                    Cont graphRead T replayRead ->
                      hsame H T ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R ∨ hsame row L ∨ hsame row C ∨
                                    hsame row Q ∨ hsame row replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont R L limitRead ∧
                                    Cont limitRead C graphRead ∧
                                      Cont graphRead T replayRead ∧ hsame H T)
                                hsame ∧
                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary lUnary cUnary _qUnary _hUnary tUnary limitRoute graphRoute replayRoute
    hsameHT _provenancePkg _namePkg
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed rUnary lUnary limitRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed limitUnary cUnary graphRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed graphUnary tUnary replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        exact ⟨source.right, limitRoute, graphRoute, replayRoute, hsameHT⟩
    }
  · exact replayUnary

end BEDC.Derived.CalculusUp
