import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_unit_tail_endpoint_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u A unitRead ->
        PkgSig bundle unitRead pkg ->
          UnaryHistory u ∧ UnaryHistory A ∧ UnaryHistory unitRead ∧
            Cont u A unitRead ∧ hsame N L ∧ PkgSig bundle unitRead pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row unitRead ∧ Cont u A unitRead)
                (fun row : BHist => hsame row unitRead ∧ PkgSig bundle unitRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute unitPkg
  obtain ⟨unaryA, _unaryF, _unaryG, unaryU, _routeB, _routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed _unaryF _unaryG routeK
  have _unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryA unitRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row unitRead ∧ Cont u A unitRead)
        (fun row : BHist => hsame row unitRead ∧ PkgSig bundle unitRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro unitRead ⟨hsame_refl unitRead, unaryUnitRead⟩
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unitRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, unitPkg⟩
    }
  exact ⟨unaryU, unaryA, unaryUnitRead, unitRoute, sameEndpoint, unitPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
