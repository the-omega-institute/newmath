import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRealSealNonescapeFromDisplayedRoute [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead readbackRead windowRead
      dyadicRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead R readbackRead ->
            Cont readbackRead W windowRead ->
              Cont windowRead D dyadicRead ->
                Cont dyadicRead S sealRead ->
                  Cont H sealRead replayRead ->
                    PkgSig bundle replayRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                              hsame row W ∨ hsame row D ∨ hsame row S ∨
                                hsame row replayRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont U F sourceRead ∧
                              Cont sourceRead E extensionRead ∧
                                Cont extensionRead R readbackRead ∧
                                  Cont readbackRead W windowRead ∧
                                    Cont windowRead D dyadicRead ∧
                                      Cont dyadicRead S sealRead ∧
                                        Cont H sealRead replayRead ∧
                                          PkgSig bundle replayRead pkg)
                          hsame ∧
                        UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute extensionRoute readbackRoute windowRoute dyadicRoute sealRoute
    replayRoute replayPkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed extensionUnary unaryR readbackRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed readbackUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH sealUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
              hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧ Cont sourceRead E extensionRead ∧
              Cont extensionRead R readbackRead ∧ Cont readbackRead W windowRead ∧
                Cont windowRead D dyadicRead ∧ Cont dyadicRead S sealRead ∧
                  Cont H sealRead replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact
        ⟨source.right, sourceRoute, extensionRoute, readbackRoute, windowRoute,
          dyadicRoute, sealRoute, replayRoute, replayPkg⟩
  }
  exact
    ⟨cert, sourceUnary, extensionUnary, readbackUnary, windowUnary, dyadicUnary,
      sealUnary, replayUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
