import BEDC.Derived.FiniteWindowRealSeparationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_namecert_surface [AskSetup] [PackageSetup]
    {x : FiniteWindowRealSeparationUp}
    {W D S R H C P N route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory N ->
                Cont W D S ->
                  Cont S R route ->
                    Cont route N endpoint ->
                      PkgSig bundle endpoint pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row endpoint ∧ Cont W D S ∧ Cont S R route ∧
                              Cont route N endpoint)
                          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _flowEq _unaryW _unaryD unaryS unaryR unaryN windowRoute separationRoute endpointRoute
    endpointPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryS unaryR separationRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary unaryN endpointRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact ⟨source.left, windowRoute, separationRoute, endpointRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

end BEDC.Derived.FiniteWindowRealSeparationUp
