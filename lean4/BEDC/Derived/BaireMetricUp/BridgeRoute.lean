import BEDC.Derived.BaireMetricUp.ObligationPublicPrefixPackage
import BEDC.Derived.BaireMetricUp.CylindricalRefinementInduction

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricBridgeRoute [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead metricRead ultrametricRead publicRead
      refinedRead : BHist}
    {spine : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead U ultrametricRead →
              Cont ultrametricRead N publicRead →
                BaireMetricRefinementSpine publicRead spine refinedRead →
                  PkgSig bundle publicRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                            hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row N ∨ hsame row refinedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                        hsame ∧
                      UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute ultrametricRoute publicRoute spineRoute
    publicPkg
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    _provenancePkg, _namePkg⟩ := carrier
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
  have refinedUnary :
      ∀ {tail : List BHist} {out : BHist},
        BaireMetricRefinementSpine publicRead tail out → UnaryHistory out := by
    intro tail
    induction tail with
    | nil =>
        intro out hsp
        exact hsp.right
    | cons step rest ih =>
        intro out hsp
        obtain ⟨prior, priorSpine, stepUnary, stepRoute⟩ := hsp
        have priorUnary : UnaryHistory prior := ih priorSpine
        exact unary_cont_closed priorUnary stepUnary stepRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    refinedUnary spineRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row refinedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedReadUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, refinedReadUnary⟩

end BEDC.Derived.BaireMetricUp
