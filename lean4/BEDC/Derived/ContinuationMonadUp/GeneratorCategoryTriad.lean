import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_generator_category_triad [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        Cont category K generator →
          PkgSig bundle generator pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row generator)
                (fun row : BHist =>
                  hsame row generator ∧ Cont L N category ∧ Cont category K generator)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle generator pkg)
                hsame ∧
              UnaryHistory generator := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute generatorPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have carrierPacket : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryK generatorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ContinuationMonadCarrier A B C f g u H K L N ∧ hsame row generator)
          (fun row : BHist =>
            hsame row generator ∧ Cont L N category ∧ Cont category K generator)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle generator pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro generator ⟨carrierPacket, hsame_refl generator⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, categoryRoute, generatorRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport unaryGenerator (hsame_symm source.right), generatorPkg⟩
    }
  exact ⟨cert, unaryGenerator⟩

end BEDC.Derived.ContinuationMonadUp
