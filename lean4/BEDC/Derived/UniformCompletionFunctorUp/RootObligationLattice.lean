import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRootObligationLattice [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F sourceRead →
        Cont sourceRead E extensionRead →
          Cont extensionRead R readbackRead →
            Cont readbackRead S sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                        hsame row W ∨ hsame row D ∨ hsame row S ∨
                          hsame row sourceRead ∨ hsame row extensionRead ∨
                            hsame row readbackRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U F sourceRead ∧
                        Cont sourceRead E extensionRead ∧
                          Cont extensionRead R readbackRead ∧
                            Cont readbackRead S sealRead ∧
                              PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceRoute extensionRoute readbackRoute sealRoute sealPkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, _unaryW, _unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
    _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed extensionUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryS sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
              hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row sourceRead ∨
                hsame row extensionRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧
              Cont sourceRead E extensionRead ∧ Cont extensionRead R readbackRead ∧
                Cont readbackRead S sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        ⟨source.right, sourceRoute, extensionRoute, readbackRoute, sealRoute,
          sealPkg⟩
  }
  exact ⟨cert, sourceUnary, extensionUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
