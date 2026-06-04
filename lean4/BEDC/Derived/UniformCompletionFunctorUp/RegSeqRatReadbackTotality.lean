import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp.RegSeqRatReadbackTotality

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRegSeqRatReadbackTotality [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead regseqRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead R regseqRead ->
            Cont regseqRead W windowRead ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                        hsame row W ∨ hsame row sourceRead ∨
                          hsame row extensionRead ∨ hsame row regseqRead ∨
                            hsame row windowRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U F sourceRead ∧
                        Cont sourceRead E extensionRead ∧
                          Cont extensionRead R regseqRead ∧
                            Cont regseqRead W windowRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory windowRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute extensionRoute regseqRoute windowRoute provenancePkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, _unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _pkgP, _pkgN⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed extensionUnary unaryR regseqRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regseqUnary unaryW windowRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
              hsame row W ∨ hsame row sourceRead ∨ hsame row extensionRead ∨
                hsame row regseqRead ∨ hsame row windowRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧
              Cont sourceRead E extensionRead ∧ Cont extensionRead R regseqRead ∧
                Cont regseqRead W windowRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro windowRead ⟨hsame_refl windowRead, windowUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, extensionRoute, regseqRoute, windowRoute,
          provenancePkg⟩
  }
  exact ⟨cert, sourceUnary, extensionUnary, regseqUnary, windowUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp.RegSeqRatReadbackTotality
