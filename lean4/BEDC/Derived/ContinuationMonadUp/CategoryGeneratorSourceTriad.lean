import BEDC.Derived.ContinuationMonadUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_category_generator_source_triad
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N sourceRead bindRead generatorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont A f sourceRead -> Cont sourceRead g bindRead ->
        Cont bindRead N generatorRead -> PkgSig bundle L pkg ->
          UnaryHistory sourceRead ∧ UnaryHistory bindRead ∧ UnaryHistory generatorRead ∧
            Cont A f sourceRead ∧ Cont sourceRead g bindRead ∧
              Cont bindRead N generatorRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row L ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∧ Cont A f sourceRead ∧ Cont sourceRead g bindRead ∧
                      Cont bindRead N generatorRead)
                  (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceRoute bindRoute generatorRoute pkgSig
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryA unaryF sourceRoute
  have bindReadUnary : UnaryHistory bindRead :=
    unary_cont_closed sourceReadUnary unaryG bindRoute
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed bindReadUnary unaryN generatorRoute
  have sourceL : (fun row : BHist => hsame row L ∧ UnaryHistory row) L := by
    exact ⟨hsame_refl L, unaryL⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row L ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row L ∧ Cont A f sourceRead ∧ Cont sourceRead g bindRead ∧
            Cont bindRead N generatorRead)
        (fun row : BHist => hsame row L ∧ PkgSig bundle L pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro L sourceL
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
      exact ⟨source.left, sourceRoute, bindRoute, generatorRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }
  exact
    ⟨sourceReadUnary, bindReadUnary, generatorReadUnary, sourceRoute, bindRoute,
      generatorRoute, cert⟩

end BEDC.Derived.ContinuationMonadUp
