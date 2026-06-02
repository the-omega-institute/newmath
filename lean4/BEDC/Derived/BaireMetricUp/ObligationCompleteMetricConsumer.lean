import BEDC.Derived.BaireMetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_obligation_complete_metric_consumer [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead limitRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont ultrametricRead R limitRead ->
        Cont limitRead U completeRead ->
          PkgSig bundle completeRead pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row completeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                      hsame row R ∨ hsame row U ∨ hsame row limitRead ∨
                        hsame row completeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont radiusRead D ultrametricRead ∧
                      Cont ultrametricRead R limitRead ∧
                        Cont limitRead U completeRead ∧ PkgSig bundle completeRead pkg)
                  hsame ∧
              UnaryHistory limitRead ∧ UnaryHistory completeRead := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier limitRoute completeRoute completePkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed ultrametricUnary unaryR limitRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed limitUnary unaryU completeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row U ∨ hsame row limitRead ∨ hsame row completeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont radiusRead D ultrametricRead ∧
              Cont ultrametricRead R limitRead ∧ Cont limitRead U completeRead ∧
                PkgSig bundle completeRead pkg)
          hsame := {
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ultrametricRoute, limitRoute, completeRoute, completePkg⟩
  }
  exact ⟨cert, limitUnary, completeUnary⟩

end BEDC.Derived.BaireMetricUp
