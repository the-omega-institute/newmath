import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCarrier_admission [AskSetup] [PackageSetup]
    {U F E R W D S H C P N handoffRead extensionRead readbackRead toleranceRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F handoffRead ->
        Cont handoffRead E extensionRead ->
          Cont extensionRead R readbackRead ->
            Cont readbackRead D toleranceRead ->
              Cont toleranceRead S sealRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                        hsame row W ∨ hsame row D ∨ hsame row S ∨
                          hsame row handoffRead ∨ hsame row extensionRead ∨
                            hsame row readbackRead ∨ hsame row toleranceRead ∨
                              hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U F handoffRead ∧
                        Cont handoffRead E extensionRead ∧
                          Cont extensionRead R readbackRead ∧
                            Cont readbackRead D toleranceRead ∧
                              Cont toleranceRead S sealRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory handoffRead ∧ UnaryHistory extensionRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier handoffRoute extensionRoute readbackRoute toleranceRoute sealRoute
  obtain ⟨unaryU, unaryF, unaryE, unaryR, _unaryW, unaryD, unaryS, _unaryH, _unaryC,
    _unaryP, _unaryN, _carrierHandoffRoute, _carrierReadbackRoute, _carrierSealRoute,
      provenancePkg, localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed unaryU unaryF handoffRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed handoffUnary unaryE extensionRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed extensionUnary unaryR readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary unaryD toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryS sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row handoffRead ∨
                hsame row extensionRead ∨ hsame row readbackRead ∨
                  hsame row toleranceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F handoffRead ∧ Cont handoffRead E extensionRead ∧
              Cont extensionRead R readbackRead ∧ Cont readbackRead D toleranceRead ∧
                Cont toleranceRead S sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        intro _row _other sameRows sourceSeal
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceSeal.left,
            unary_transport sourceSeal.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceSeal
      repeat right
      exact sourceSeal.left
    ledger_sound := by
      intro _row sourceSeal
      exact
        ⟨sourceSeal.right, handoffRoute, extensionRoute, readbackRoute, toleranceRoute,
          sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, handoffUnary, extensionUnary, readbackUnary, toleranceUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
