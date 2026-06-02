import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricRootUltrametricCylinderCarrier [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead ultrametricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg ->
      Cont S B prefixRead ->
        Cont prefixRead W radiusRead ->
          Cont radiusRead D metricRead ->
            Cont metricRead U ultrametricRead ->
              PkgSig bundle ultrametricRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row ultrametricRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                        hsame row R ∨ hsame row U ∨ hsame row prefixRead ∨
                          hsame row radiusRead ∨ hsame row metricRead ∨
                            hsame row ultrametricRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S B prefixRead ∧
                        Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                          Cont metricRead U ultrametricRead ∧
                            PkgSig bundle ultrametricRead pkg)
                    hsame ∧
                  UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory ultrametricRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute ultrametricRoute ultrametricPkg
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierRoute, _carrierMetricRoute, _provenancePkg,
    _namePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed metricUnary uUnary ultrametricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ultrametricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row U ∨ hsame row prefixRead ∨
                hsame row radiusRead ∨ hsame row metricRead ∨ hsame row ultrametricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead U ultrametricRead ∧
                PkgSig bundle ultrametricRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ultrametricRead ⟨hsame_refl ultrametricRead, ultrametricUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, ultrametricRoute,
          ultrametricPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, ultrametricUnary⟩

end BEDC.Derived.BaireMetricUp
