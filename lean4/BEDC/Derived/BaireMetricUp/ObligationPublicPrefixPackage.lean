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

theorem BaireMetricObligationPublicPrefixPackage [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead metricRead ultrametricRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead U ultrametricRead →
              Cont ultrametricRead N publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row S ∨ hsame row B ∨ hsame row D ∨
                          hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S B prefixRead ∧
                          Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                            Cont metricRead U ultrametricRead ∧
                              Cont ultrametricRead N publicRead ∧
                                PkgSig bundle publicRead pkg)
                      hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory ultrametricRead ∧
                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute ultrametricRoute publicRoute publicPkg
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, _provenancePkg,
    _namePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed metricUnary uUnary ultrametricRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ultrametricUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row S ∨ hsame row B ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead U ultrametricRead ∧
                Cont ultrametricRead N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, ultrametricRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, ultrametricUnary, publicUnary⟩

end BEDC.Derived.BaireMetricUp
