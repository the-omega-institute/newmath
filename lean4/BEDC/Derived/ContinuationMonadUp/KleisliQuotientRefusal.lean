import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_kleisli_quotient_refusal
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        Cont category N generator →
          PkgSig bundle generator pkg →
            SemanticNameCert
              (fun row : BHist => hsame row generator ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont L N category ∧ Cont category N generator ∧ hsame row generator)
              (fun row : BHist => hsame row generator ∧ PkgSig bundle generator pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute generatorPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, _routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have sourceGenerator :
      (fun row : BHist => hsame row generator ∧ UnaryHistory row) generator := by
    exact ⟨hsame_refl generator, unaryGenerator⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro generator sourceGenerator
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨categoryRoute, generatorRoute, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, generatorPkg⟩
  }

end BEDC.Derived.ContinuationMonadUp
