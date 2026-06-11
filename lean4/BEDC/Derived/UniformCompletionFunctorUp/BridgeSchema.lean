import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorBridgeSchema [AskSetup] [PackageSetup]
    {U F E R W D S H C P N publicRead sourceRead cauchyRead extensionRead sealRead
      consumerRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont S N publicRead ->
        Cont U F sourceRead ->
          Cont sourceRead R cauchyRead ->
            Cont cauchyRead W extensionRead ->
              Cont extensionRead S sealRead ->
                Cont sealRead N consumerRead ->
                  Cont publicRead consumerRead bridgeRead ->
                    PkgSig bundle bridgeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                              hsame row W ∨ hsame row D ∨ hsame row S ∨
                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                  hsame row N ∨ hsame row publicRead ∨
                                    hsame row consumerRead ∨ hsame row bridgeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S N publicRead ∧
                              Cont U F sourceRead ∧ Cont sourceRead R cauchyRead ∧
                                Cont cauchyRead W extensionRead ∧
                                  Cont extensionRead S sealRead ∧
                                    Cont sealRead N consumerRead ∧
                                      Cont publicRead consumerRead bridgeRead ∧
                                        PkgSig bundle bridgeRead pkg)
                          hsame ∧
                        UnaryHistory publicRead ∧ UnaryHistory sourceRead ∧
                          UnaryHistory cauchyRead ∧ UnaryHistory extensionRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory consumerRead ∧
                              UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute sourceRoute cauchyRoute extensionRoute sealRoute consumerRoute
    bridgeRoute bridgePkg
  obtain ⟨unaryU, unaryF, _unaryE, unaryR, unaryW, _unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryS unaryN publicRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed sourceUnary unaryR cauchyRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed cauchyUnary unaryW extensionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed extensionUnary unaryS sealRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary unaryN consumerRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary consumerUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead ∨
                  hsame row consumerRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S N publicRead ∧ Cont U F sourceRead ∧
              Cont sourceRead R cauchyRead ∧ Cont cauchyRead W extensionRead ∧
                Cont extensionRead S sealRead ∧ Cont sealRead N consumerRead ∧
                  Cont publicRead consumerRead bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, publicRoute, sourceRoute, cauchyRoute, extensionRoute, sealRoute,
          consumerRoute, bridgeRoute, bridgePkg⟩
  }
  exact
    ⟨cert, publicUnary, sourceUnary, cauchyUnary, extensionUnary, sealUnary,
      consumerUnary, bridgeUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
