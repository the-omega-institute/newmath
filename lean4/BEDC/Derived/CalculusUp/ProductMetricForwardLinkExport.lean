import BEDC.Derived.CalculusUp.ProductMetricRealRoute

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusProductMetricForwardLinkExport [AskSetup] [PackageSetup]
    {cauchyProduct metric stream regSeq dyadic real productRead streamRead regularRead
      dyadicRead modulusRead terminalRead realRouteRead exportRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory cauchyProduct ->
      UnaryHistory metric ->
        UnaryHistory stream ->
          UnaryHistory regSeq ->
            UnaryHistory dyadic ->
              UnaryHistory real ->
                Cont cauchyProduct metric productRead ->
                  Cont productRead stream streamRead ->
                    Cont streamRead regSeq regularRead ->
                      Cont regularRead dyadic dyadicRead ->
                        Cont dyadicRead metric modulusRead ->
                          Cont modulusRead real terminalRead ->
                            Cont terminalRead real realRouteRead ->
                              Cont realRouteRead stream exportRead ->
                                PkgSig bundle provenance pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row exportRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row cauchyProduct ∨ hsame row metric ∨
                                          hsame row stream ∨ hsame row regSeq ∨
                                            hsame row dyadic ∨ hsame row modulusRead ∨
                                              hsame row terminalRead ∨
                                                hsame row realRouteRead ∨
                                                  hsame row exportRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont regularRead dyadic dyadicRead ∧
                                            Cont dyadicRead metric modulusRead ∧
                                              Cont modulusRead real terminalRead ∧
                                                Cont terminalRead real realRouteRead ∧
                                                  Cont realRouteRead stream exportRead ∧
                                                    PkgSig bundle provenance pkg)
                                      hsame ∧
                                    UnaryHistory productRead ∧ UnaryHistory streamRead ∧
                                      UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
                                        UnaryHistory modulusRead ∧ UnaryHistory terminalRead ∧
                                          UnaryHistory realRouteRead ∧
                                            UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro cauchyUnary metricUnary streamUnary regSeqUnary dyadicUnary realUnary productRoute
    streamRoute regularRoute dyadicRoute modulusRoute terminalRoute realRoute exportRoute
    provenancePkg
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed cauchyUnary metricUnary productRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed productReadUnary streamUnary streamRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed streamReadUnary regSeqUnary regularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularReadUnary dyadicUnary dyadicRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed dyadicReadUnary metricUnary modulusRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed modulusReadUnary realUnary terminalRoute
  have realRouteReadUnary : UnaryHistory realRouteRead :=
    unary_cont_closed terminalReadUnary realUnary realRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed realRouteReadUnary streamUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cauchyProduct ∨ hsame row metric ∨ hsame row stream ∨
              hsame row regSeq ∨ hsame row dyadic ∨ hsame row modulusRead ∨
                hsame row terminalRead ∨ hsame row realRouteRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regularRead dyadic dyadicRead ∧
              Cont dyadicRead metric modulusRead ∧ Cont modulusRead real terminalRead ∧
                Cont terminalRead real realRouteRead ∧ Cont realRouteRead stream exportRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, modulusRoute, terminalRoute, realRoute,
          exportRoute, provenancePkg⟩
  }
  exact
    ⟨cert, productReadUnary, streamReadUnary, regularReadUnary, dyadicReadUnary,
      modulusReadUnary, terminalReadUnary, realRouteReadUnary, exportReadUnary⟩

end BEDC.Derived.CalculusUp
