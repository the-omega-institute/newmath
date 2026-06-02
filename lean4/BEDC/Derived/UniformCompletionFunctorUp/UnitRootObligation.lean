import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCarrier_unit_root_obligation [AskSetup] [PackageSetup]
    {U F E R W D S H C P N unitRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F unitRead ->
        Cont unitRead R sealRead ->
          Cont sealRead N namedRead ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row F ∨ hsame row R ∨ hsame row S ∨
                      hsame row N ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont U F unitRead ∧
                      Cont unitRead R sealRead ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory unitRead ∧ UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier unitRoute sealRoute namedRoute namedPkg
  obtain ⟨unaryU, unaryF, _unaryE, unaryR, _unaryW, _unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unitUnary unaryR sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row R ∨ hsame row S ∨
              hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F unitRead ∧ Cont unitRead R sealRead ∧
              PkgSig bundle namedRead pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, unitRoute, sealRoute, namedPkg⟩
    }
  exact ⟨cert, unitUnary, sealUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
