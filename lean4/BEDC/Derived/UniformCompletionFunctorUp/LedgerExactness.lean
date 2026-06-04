import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorLedgerExactness [AskSetup] [PackageSetup]
    {U F E R W D S H C P N handoffRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F handoffRead ->
        Cont H C replayRead ->
          PkgSig bundle replayRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                    hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row handoffRead ∨ hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont U F handoffRead ∧ Cont H C replayRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle replayRead pkg)
                hsame ∧ UnaryHistory handoffRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier handoffRoute replayRoute replayPkg
  obtain ⟨uUnary, fUnary, _eUnary, _rUnary, _wUnary, _dUnary, _sUnary, hUnary,
    cUnary, _pUnary, _nUnary, _sourceRoute, _readbackRoute, _sealRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed uUnary fUnary handoffRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
              hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row handoffRead ∨
                  hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F handoffRead ∧ Cont H C replayRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle replayRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffRoute, replayRoute, provenancePkg, localNamePkg, replayPkg⟩
  }
  exact ⟨cert, handoffUnary, replayUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
