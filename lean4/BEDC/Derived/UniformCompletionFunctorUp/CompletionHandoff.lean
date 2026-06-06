import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCompletionHandoff [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead windowRead dyadicRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead W windowRead ->
            Cont windowRead D dyadicRead ->
              Cont dyadicRead S sealRead ->
                Cont sealRead N namedRead ->
                  PkgSig bundle namedRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
                            hsame row D ∨ hsame row S ∨ hsame row N ∨
                              hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont U F sourceRead ∧
                            Cont sourceRead E extensionRead ∧
                              Cont extensionRead W windowRead ∧
                                Cont windowRead D dyadicRead ∧
                                  Cont dyadicRead S sealRead ∧
                                    PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                        UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute extensionRoute windowRoute dyadicRoute sealRoute namedRoute
    namedPkg
  obtain ⟨unaryU, unaryF, unaryE, _unaryR, unaryW, unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed extensionUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨ hsame row D ∨
              hsame row S ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧ Cont sourceRead E extensionRead ∧
              Cont extensionRead W windowRead ∧ Cont windowRead D dyadicRead ∧
                Cont dyadicRead S sealRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, extensionRoute, windowRoute, dyadicRoute,
          sealRoute, namedPkg⟩
  }
  exact
    ⟨cert, sourceUnary, extensionUnary, windowUnary, dyadicUnary, sealUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
