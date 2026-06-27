import BEDC.Derived.PrecompactMetricUp

namespace BEDC.Derived.PrecompactMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PrecompactMetric_mature_completion_reflection [AskSetup] [PackageSetup]
    {X D N F R M H C G Q netRead filterRead routeRead completionRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PrecompactMetricCarrier X D N F R M H C G Q bundle pkg ->
      Cont N M netRead ->
        Cont M F filterRead ->
          Cont filterRead G routeRead ->
            Cont routeRead C completionRead ->
              Cont completionRead Q bridgeRead ->
                PkgSig bundle bridgeRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row D ∨ hsame row N ∨ hsame row F ∨
                          hsame row R ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                            hsame row G ∨ hsame row Q ∨ hsame row netRead ∨
                              hsame row filterRead ∨ hsame row routeRead ∨
                                hsame row completionRead ∨ hsame row bridgeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont N M netRead ∧ Cont M F filterRead ∧
                          Cont filterRead G routeRead ∧ Cont routeRead C completionRead ∧
                            Cont completionRead Q bridgeRead ∧ PkgSig bundle Q pkg ∧
                              PkgSig bundle bridgeRead pkg)
                      hsame ∧
                    UnaryHistory netRead ∧ UnaryHistory filterRead ∧
                      UnaryHistory routeRead ∧ UnaryHistory completionRead ∧
                        UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: PrecompactMetricCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier netRoute filterRoute routeRoute completionRoute bridgeRoute bridgePkg
  obtain ⟨_xUnary, _dUnary, nUnary, fUnary, _rUnary, mUnary, _hUnary, cUnary,
    gUnary, qUnary, provenancePkg⟩ := carrier
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed nUnary mUnary netRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed mUnary fUnary filterRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed filterUnary gUnary routeRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed routeUnary cUnary completionRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed completionUnary qUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row D ∨ hsame row N ∨ hsame row F ∨ hsame row R ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨ hsame row Q ∨
                hsame row netRead ∨ hsame row filterRead ∨ hsame row routeRead ∨
                  hsame row completionRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N M netRead ∧ Cont M F filterRead ∧
              Cont filterRead G routeRead ∧ Cont routeRead C completionRead ∧
                Cont completionRead Q bridgeRead ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, netRoute, filterRoute, routeRoute, completionRoute, bridgeRoute,
          provenancePkg, bridgePkg⟩
  }
  exact
    ⟨cert, netUnary, filterUnary, routeUnary, completionUnary, bridgeUnary⟩

end BEDC.Derived.PrecompactMetricUp
