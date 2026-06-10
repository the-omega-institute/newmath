import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCofinalWindowFactorization [AskSetup] [PackageSetup]
    {U F E R W D S H C P N handoffRead windowRead cofinalRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F handoffRead ->
        Cont handoffRead W windowRead ->
          Cont windowRead D cofinalRead ->
            Cont cofinalRead S terminalRead ->
              PkgSig bundle terminalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
                        hsame row R ∨ hsame row D ∨ hsame row S ∨
                          hsame row handoffRead ∨ hsame row windowRead ∨
                            hsame row cofinalRead ∨ hsame row terminalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U F handoffRead ∧
                        Cont handoffRead W windowRead ∧
                          Cont windowRead D cofinalRead ∧
                            Cont cofinalRead S terminalRead ∧
                              PkgSig bundle terminalRead pkg)
                    hsame ∧
                  UnaryHistory handoffRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory cofinalRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier handoffRoute windowRoute cofinalRoute terminalRoute terminalPkg
  obtain ⟨unaryU, unaryF, _unaryE, _unaryR, unaryW, unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _sourceRoute, _readbackRoute, _sealRoute,
      _provenancePkg, _localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed unaryU unaryF handoffRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed handoffUnary unaryW windowRoute
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed windowUnary unaryD cofinalRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed cofinalUnary unaryS terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row S ∨ hsame row handoffRead ∨
                hsame row windowRead ∨ hsame row cofinalRead ∨
                  hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F handoffRead ∧
              Cont handoffRead W windowRead ∧ Cont windowRead D cofinalRead ∧
                Cont cofinalRead S terminalRead ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
        ⟨source.right, handoffRoute, windowRoute, cofinalRoute, terminalRoute,
          terminalPkg⟩
  }
  exact ⟨cert, handoffUnary, windowUnary, cofinalUnary, terminalUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
