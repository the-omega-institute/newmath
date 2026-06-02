import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRealSealNonescape [AskSetup] [PackageSetup]
    {U F E R W D S H C P N readbackRead toleranceRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont R W readbackRead ->
        Cont readbackRead D toleranceRead ->
          Cont toleranceRead S sealRead ->
            Cont H sealRead replayRead ->
              PkgSig bundle replayRead pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                      hsame row W ∨ hsame row D ∨ hsame row S ∨
                        hsame row toleranceRead ∨ hsame row sealRead ∨
                          hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
                  hsame ∧
                    UnaryHistory readbackRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier readbackRoute toleranceRoute sealRoute replayRoute replayPkg
  obtain ⟨_unaryU, _unaryF, _unaryE, unaryR, unaryW, unaryD, unaryS, unaryH,
    _unaryC, _unaryP, _unaryN, _sourceRoute, _readbackRoute, _sealCarrierRoute,
    provenancePkg, _localNamePkg⟩ := carrier
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed unaryR unaryW readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary unaryD toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryS sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH sealUnary replayRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
            hsame row W ∨ hsame row D ∨ hsame row S ∨
              hsame row toleranceRead ∨ hsame row sealRead ∨ hsame row replayRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, replayPkg⟩
  }
  exact ⟨cert, readbackUnary, toleranceUnary, sealUnary, replayUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
