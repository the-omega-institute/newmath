import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCompletionConsumerFrontier [AskSetup] [PackageSetup]
    {U F E R W D S H C P N frontierRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F E ->
        Cont E R W ->
          Cont W D S ->
            Cont S H frontierRead ->
              Cont frontierRead C named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row named ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                          hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row frontierRead ∨ hsame row named)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle named pkg)
                      hsame ∧
                    UnaryHistory frontierRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier _sourceRoute _readbackRoute _sealRoute frontierRoute namedRoute namedPkg
  obtain ⟨_unaryU, _unaryF, _unaryE, _unaryR, _unaryW, _unaryD, unaryS, unaryH,
    unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
    _carrierSealRoute, provenancePkg, _localNamePkg⟩ := carrier
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed unaryS unaryH frontierRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed frontierUnary unaryC namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row frontierRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, frontierUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
