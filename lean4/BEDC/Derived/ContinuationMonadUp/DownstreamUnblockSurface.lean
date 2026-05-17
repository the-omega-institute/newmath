import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_downstream_unblock_surface [AskSetup] [PackageSetup]
    {A B C f g u H K L N consumer : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory consumer ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont L N consumer ∧ hsame N L ∧
                  PkgSig bundle consumer pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                      (fun row : BHist => hsame row consumer ∧ Cont L N consumer)
                      (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier downstreamRoute consumerPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryL unaryN downstreamRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, unaryConsumer⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist => hsame row consumer ∧ Cont L N consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer sourceConsumer
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, downstreamRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, consumerPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryConsumer,
      routeB, routeC, routeK, routeL, downstreamRoute, sameEndpoint, consumerPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
