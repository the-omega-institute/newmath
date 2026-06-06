import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorFunctoriality [AskSetup] [PackageSetup]
    {U F E R W D S H C P N unitRead bindRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F unitRead ->
        Cont unitRead E bindRead ->
          Cont bindRead S classifierRead ->
            PkgSig bundle classifierRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                      hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row unitRead ∨
                        hsame row bindRead ∨ hsame row classifierRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle classifierRead pkg ∧
                      Cont unitRead E bindRead)
                  hsame ∧ UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unitRoute bindRoute classifierRoute classifierPkg
  obtain ⟨unaryU, unaryF, unaryE, _unaryR, _unaryW, _unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
    _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have bindUnary : UnaryHistory bindRead :=
    unary_cont_closed unitUnary unaryE bindRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed bindUnary unaryS classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row unitRead ∨ hsame row bindRead ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle classifierRead pkg ∧
              Cont unitRead E bindRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro classifierRead ⟨hsame_refl classifierRead, classifierUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierPkg, bindRoute⟩
  }
  exact ⟨cert, unitUnary, bindUnary, classifierUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
