import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorScopedL10ObligationRoute [AskSetup] [PackageSetup]
    {U F E R W D S H C P N scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F E →
        Cont R W D →
          Cont H C scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                      hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row scopedRead)
                  (fun _row : BHist =>
                    PkgSig bundle scopedRead pkg ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg ∧ Cont U F E ∧ Cont R W D ∧
                        Cont H C scopedRead)
                  hsame ∧
                UnaryHistory scopedRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute readbackRoute replayRoute scopedPkg
  obtain ⟨_unaryU, _unaryF, _unaryE, _unaryR, _unaryW, _unaryD, _unaryS, unaryH,
    unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
    _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed unaryH unaryC replayRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row scopedRead)
          (fun _row : BHist =>
            PkgSig bundle scopedRead pkg ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg ∧ Cont U F E ∧ Cont R W D ∧
                Cont H C scopedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨scopedPkg, provenancePkg, localNamePkg, sourceRoute, readbackRoute,
          replayRoute⟩
  }
  exact ⟨cert, scopedUnary, localNamePkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
