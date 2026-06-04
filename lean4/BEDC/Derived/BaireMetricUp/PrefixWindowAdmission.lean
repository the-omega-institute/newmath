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

def BaireMetricCarrier [AskSetup] [PackageSetup]
    (B W D R U S H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory U ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S B W ∧ Cont W D R ∧
        Cont R U C ∧ Cont C N P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BaireMetricCarrier_prefix_window_admission [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg ->
      Cont S B prefixRead ->
        Cont prefixRead W radiusRead ->
          UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧ Cont S B prefixRead ∧
            Cont prefixRead W radiusRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier prefixRoute radiusRoute
  obtain ⟨bUnary, wUnary, _dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    carrierPkg, _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  exact ⟨prefixUnary, radiusUnary, prefixRoute, radiusRoute, carrierPkg⟩

theorem BaireMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B W D R U S H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row C ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row U ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B W ∧ Cont W D R ∧ PkgSig bundle P pkg)
          hsame ∧ UnaryHistory W ∧ UnaryHistory D ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_bUnary, wUnary, dUnary, _rUnary, _uUnary, _sUnary, _hUnary, cUnary,
    _pUnary, _nUnary, carrierSBW, carrierWDR, _carrierRUC, _carrierCNP, carrierPkg,
    carrierNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row C ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row U ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B W ∧ Cont W D R ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro C ⟨hsame_refl C, cUnary⟩
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
                      (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierSBW, carrierWDR, carrierPkg⟩
  }
  exact ⟨cert, wUnary, dUnary, carrierNamePkg⟩

theorem BaireMetricCarrier_complete_metric_handoff [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            PkgSig bundle metricRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                      hsame row R ∨ hsame row U ∨ hsame row prefixRead ∨
                        hsame row radiusRead ∨ hsame row metricRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S B prefixRead ∧
                      Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                        PkgSig bundle metricRead pkg)
                  hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute metricPkg
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    _carrierPkg, _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row prefixRead ∨ hsame row radiusRead ∨
                hsame row metricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ PkgSig bundle metricRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricRead ⟨hsame_refl metricRead, metricUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, radiusRoute, metricRoute, metricPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary⟩

theorem BaireMetricNamecertObligationSurface [AskSetup] [PackageSetup]
    {B W D R U S H C P N radiusRead ultrametricRead metricRead obligation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B radiusRead →
        Cont radiusRead D ultrametricRead →
          Cont ultrametricRead R metricRead →
            Cont metricRead N obligation →
              PkgSig bundle obligation pkg →
                SemanticNameCert (fun row : BHist => hsame row obligation)
                    (fun row : BHist =>
                      Cont metricRead N row ∧ PkgSig bundle obligation pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligation pkg)
                    hsame ∧
                  UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory obligation ∧
                      PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceBaseRadius radiusDepthUltrametric ultrametricRootMetric
    metricNameObligation obligationPkg
  obtain ⟨bUnary, _wUnary, dUnary, rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, carrierPkg,
    _carrierNamePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed sUnary bUnary sourceBaseRadius
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary dUnary radiusDepthUltrametric
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary rUnary ultrametricRootMetric
  have obligationUnary : UnaryHistory obligation :=
    unary_cont_closed metricUnary nUnary metricNameObligation
  have cert :
      SemanticNameCert (fun row : BHist => hsame row obligation)
          (fun row : BHist => Cont metricRead N row ∧ PkgSig bundle obligation pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligation pkg) hsame := {
    core := {
      carrier_inhabited := Exists.intro obligation (hsame_refl obligation)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport metricNameObligation (hsame_symm source),
          obligationPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport obligationUnary (hsame_symm source), obligationPkg⟩
  }
  exact
    ⟨cert, radiusUnary, ultrametricUnary, metricUnary, obligationUnary, carrierPkg⟩

theorem BaireMetricCarrier_root_observation [AskSetup] [PackageSetup]
    {B W D R U S H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg ->
      UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧
        Cont S B W ∧ Cont W D R ∧ Cont R U C ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, carrierSBW, carrierWDR, carrierRUC, _carrierCNP, carrierPkg,
    carrierNamePkg⟩ := carrier
  exact
    ⟨sUnary, bUnary, wUnary, dUnary, carrierSBW, carrierWDR, carrierRUC, carrierPkg,
      carrierNamePkg⟩

theorem BaireMetricCompleteUltrametricConsumerReadiness [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead strongRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead R strongRead →
              Cont strongRead U consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                          hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S B prefixRead ∧
                          Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                            Cont metricRead R strongRead ∧ Cont strongRead U consumerRead ∧
                              PkgSig bundle consumerRead pkg)
                      hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory strongRead ∧
                      UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute strongRoute consumerRoute consumerPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, uUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, _carrierPkg,
    _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed metricUnary rUnary strongRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed strongUnary uUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead R strongRead ∧
                Cont strongRead U consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, strongRoute, consumerRoute,
          consumerPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, strongUnary, consumerUnary⟩

theorem BaireMetricStreamNameUltrametricObligation [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead strongRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead U strongRead →
              PkgSig bundle strongRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row strongRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                        hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row strongRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S B prefixRead ∧
                        Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                          Cont metricRead U strongRead ∧ PkgSig bundle strongRead pkg)
                    hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory metricRead ∧ UnaryHistory strongRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute strongRoute strongPkg
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, uUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, _carrierPkg,
    _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed metricUnary uUnary strongRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row strongRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row strongRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead U strongRead ∧
                PkgSig bundle strongRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro strongRead ⟨hsame_refl strongRead, strongUnary⟩
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
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, strongRoute, strongPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, strongUnary⟩

end BEDC.Derived.BaireMetricUp
