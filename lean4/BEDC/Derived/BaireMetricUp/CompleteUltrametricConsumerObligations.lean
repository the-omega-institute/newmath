import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCompleteUltrametricConsumerObligations [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead ultraRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S -> UnaryHistory B -> UnaryHistory W -> UnaryHistory D ->
      UnaryHistory R -> UnaryHistory U -> Cont S B prefixRead ->
        Cont prefixRead W radiusRead -> Cont radiusRead D metricRead ->
          Cont metricRead R ultraRead -> Cont ultraRead U completeRead ->
            PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row completeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                    hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row completeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S B prefixRead ∧
                    Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                      Cont metricRead R ultraRead ∧ Cont ultraRead U completeRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sUnary bUnary wUnary dUnary rUnary uUnary prefixRoute radiusRoute metricRoute
    ultraRoute completeRoute provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have ultraUnary : UnaryHistory ultraRead :=
    unary_cont_closed metricUnary rUnary ultraRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed ultraUnary uUnary completeRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro completeRead ⟨hsame_refl completeRead, completeUnary⟩
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, ultraRoute, completeRoute,
          provenancePkg, namePkg⟩
  }

end BEDC.Derived.BaireMetricUp
