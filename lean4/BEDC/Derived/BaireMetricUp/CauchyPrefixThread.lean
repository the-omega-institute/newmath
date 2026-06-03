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

theorem BaireMetricCauchyPrefixThread [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead metricRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead R metricRead →
        Cont metricRead U cauchyRead →
          PkgSig bundle cauchyRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                    hsame row R ∨ hsame row U ∨ hsame row metricRead ∨
                      hsame row cauchyRead)
                (fun row : BHist =>
                  hsame row cauchyRead ∧ Cont ultrametricRead R metricRead ∧
                    Cont metricRead U cauchyRead ∧ PkgSig bundle cauchyRead pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory cauchyRead ∧
                Cont S B radiusRead ∧ Cont radiusRead D ultrametricRead ∧
                  Cont ultrametricRead R metricRead ∧ Cont metricRead U cauchyRead := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier metricRoute cauchyRoute cauchyPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, _provenancePkg,
    _localNamePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary unaryR metricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed metricUnary unaryU cauchyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row U ∨ hsame row metricRead ∨
                hsame row cauchyRead)
          (fun row : BHist =>
            hsame row cauchyRead ∧ Cont ultrametricRead R metricRead ∧
              Cont metricRead U cauchyRead ∧ PkgSig bundle cauchyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead
        ⟨hsame_refl cauchyRead, cauchyUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, metricRoute, cauchyRoute, cauchyPkg⟩
  }
  exact
    ⟨cert, metricUnary, cauchyUnary, radiusRoute, ultrametricRoute, metricRoute,
      cauchyRoute⟩

end BEDC.Derived.BaireMetricUp
