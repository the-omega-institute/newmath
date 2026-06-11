import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRegSeqRealBridge [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead streamRead regRead dyadicRead sealRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F sourceRead →
        Cont sourceRead W streamRead →
          Cont streamRead R regRead →
            Cont regRead D dyadicRead →
              Cont dyadicRead S sealRead →
                Cont sealRead N bridgeRead →
                  PkgSig bundle bridgeRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row U ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨
                            hsame row D ∨ hsame row S ∨ hsame row N ∨
                              hsame row bridgeRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont U F sourceRead ∧
                            Cont sourceRead W streamRead ∧ Cont streamRead R regRead ∧
                              Cont regRead D dyadicRead ∧ Cont dyadicRead S sealRead ∧
                                Cont sealRead N bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                        hsame ∧
                      UnaryHistory sourceRead ∧ UnaryHistory streamRead ∧
                        UnaryHistory regRead ∧ UnaryHistory dyadicRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute streamRoute regRoute dyadicRoute sealRoute bridgeRoute bridgePkg
  obtain ⟨unaryU, unaryF, _unaryE, unaryR, unaryW, unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sourceUnary unaryW streamRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed streamUnary unaryR regRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sealUnary unaryN bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row S ∨ hsame row N ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F sourceRead ∧ Cont sourceRead W streamRead ∧
              Cont streamRead R regRead ∧ Cont regRead D dyadicRead ∧
                Cont dyadicRead S sealRead ∧ Cont sealRead N bridgeRead ∧
                  PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, streamRoute, regRoute, dyadicRoute, sealRoute,
          bridgeRoute, bridgePkg⟩
  }
  exact
    ⟨cert, sourceUnary, streamUnary, regUnary, dyadicUnary, sealUnary, bridgeUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
