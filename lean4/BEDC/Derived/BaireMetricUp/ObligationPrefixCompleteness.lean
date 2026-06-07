import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_obligation_prefix_completeness [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead windowRead radiusRead metricRead ultraRead
      structuralRead namedRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory B ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory U ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont S B prefixRead ->
                          Cont prefixRead W windowRead ->
                            Cont windowRead D radiusRead ->
                              Cont radiusRead R metricRead ->
                                Cont metricRead U ultraRead ->
                                  Cont H C structuralRead ->
                                    Cont P N namedRead ->
                                      Cont ultraRead structuralRead completeRead ->
                                        PkgSig bundle P pkg ->
                                          PkgSig bundle N pkg ->
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row completeRead ∧
                                                    UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row S ∨ hsame row B ∨
                                                    hsame row W ∨ hsame row D ∨
                                                      hsame row R ∨ hsame row U ∨
                                                        hsame row H ∨ hsame row C ∨
                                                          hsame row P ∨ hsame row N ∨
                                                            hsame row completeRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    Cont S B prefixRead ∧
                                                      Cont prefixRead W windowRead ∧
                                                        Cont windowRead D radiusRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                                hsame ∧ UnaryHistory prefixRead ∧
                                              UnaryHistory windowRead ∧
                                                UnaryHistory completeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sUnary bUnary wUnary dUnary rUnary uUnary hUnary cUnary pUnary nUnary prefixRoute
    windowRoute radiusRoute metricRoute ultraRoute structuralRoute namedRoute completeRoute
    pkgP pkgN
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed prefixUnary wUnary windowRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed windowUnary dUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary rUnary metricRoute
  have ultraUnary : UnaryHistory ultraRead :=
    unary_cont_closed metricUnary uUnary ultraRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have _namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namedRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed ultraUnary structuralUnary completeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row completeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W windowRead ∧
              Cont windowRead D radiusRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completeRead ⟨hsame_refl completeRead, completeUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, windowRoute, radiusRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, prefixUnary, windowUnary, completeUnary⟩

end BEDC.Derived.BaireMetricUp
