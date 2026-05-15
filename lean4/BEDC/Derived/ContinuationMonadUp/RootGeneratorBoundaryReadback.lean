import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_generator_boundary_readback
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator K boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                    UnaryHistory boundaryRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                        Cont category N generator ∧ Cont generator K boundaryRead ∧
                          hsame N L ∧ PkgSig bundle boundaryRead pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                Cont category N generator ∧ Cont generator K row)
                              (fun row : BHist =>
                                hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute boundaryRoute boundaryPkg
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
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryBoundary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryGenerator unaryK boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, unaryBoundary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
        (fun row : BHist => Cont category N generator ∧ Cont generator K row)
        (fun row : BHist => hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨generatorRoute,
            cont_result_hsame_transport boundaryRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, boundaryPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategory, unaryGenerator, unaryBoundary, routeB, routeC, routeK, routeL,
      categoryRoute, generatorRoute, boundaryRoute, sameEndpoint, boundaryPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
