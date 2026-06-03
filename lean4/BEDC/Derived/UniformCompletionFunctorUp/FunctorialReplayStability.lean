import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorFunctorialReplayStability [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead regseqRead windowRead dyadicRead
      sealRead transported replayed named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead R regseqRead ->
            Cont regseqRead W windowRead ->
              Cont windowRead D dyadicRead ->
                Cont dyadicRead S sealRead ->
                  Cont sealRead H transported ->
                    Cont transported C replayed ->
                      Cont replayed N named ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row named ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row U ∨ hsame row F ∨ hsame row E ∨
                                    hsame row R ∨ hsame row W ∨ hsame row D ∨
                                      hsame row S ∨ hsame row H ∨ hsame row C ∨
                                        hsame row N ∨ hsame row named)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont sealRead H transported ∧
                                    Cont transported C replayed ∧ Cont replayed N named ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory transported ∧ UnaryHistory replayed ∧
                                UnaryHistory named := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute extensionRoute regseqRoute windowRoute dyadicRoute sealRoute
    transportedRoute replayRoute namedRoute provenancePkg localNamePkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, unaryH, unaryC,
    _unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute, _carrierSealRoute,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed extensionUnary unaryR regseqRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regseqUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary unaryH transportedRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary unaryC replayRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayedUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
              hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                hsame row C ∨ hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sealRead H transported ∧
              Cont transported C replayed ∧ Cont replayed N named ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact
        ⟨source.right, transportedRoute, replayRoute, namedRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, transportedUnary, replayedUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
