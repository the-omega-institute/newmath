import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricBaireSpacePrefixDensityRoute [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead R densityRead →
              PkgSig bundle densityRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                        hsame row R ∨ hsame row densityRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S B prefixRead ∧
                        Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                          Cont metricRead R densityRead ∧ PkgSig bundle densityRead pkg)
                    hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory metricRead ∧ UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute densityRoute densityPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, _uUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, _carrierPkg,
    _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed metricUnary rUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead R densityRead ∧
                PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, densityRoute,
          densityPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, densityUnary⟩

end BEDC.Derived.BaireMetricUp
