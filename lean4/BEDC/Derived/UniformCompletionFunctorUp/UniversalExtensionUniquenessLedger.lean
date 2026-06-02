import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorUniversalExtensionUniquenessLedger [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead uniquenessRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead E uniquenessRead ->
            Cont uniquenessRead N namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row N ∨
                        hsame row sourceRead ∨ hsame row extensionRead ∨
                          hsame row uniquenessRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U F sourceRead ∧
                        Cont sourceRead E extensionRead ∧
                          Cont extensionRead E uniquenessRead ∧
                            Cont uniquenessRead N namedRead ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                    UnaryHistory uniquenessRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute extensionRoute uniquenessRoute namedRoute namedPkg
  obtain ⟨uUnary, fUnary, eUnary, _rUnary, _wUnary, _dUnary, _sUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _carrierSource, _carrierReadback, _carrierSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed uUnary fUnary sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary eUnary extensionRoute
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed extensionUnary eUnary uniquenessRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed uniquenessUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row N ∨
              hsame row sourceRead ∨ hsame row extensionRead ∨
                hsame row uniquenessRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧ Cont sourceRead E extensionRead ∧
              Cont extensionRead E uniquenessRead ∧ Cont uniquenessRead N namedRead ∧
                PkgSig bundle namedRead pkg)
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, extensionRoute, uniquenessRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, sourceUnary, extensionUnary, uniquenessUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
