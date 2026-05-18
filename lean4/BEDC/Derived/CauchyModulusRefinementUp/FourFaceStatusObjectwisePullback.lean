import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_four_face_status_objectwise_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n dyadicFace streamFace regseqFace realFace terminal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont u v dyadicFace ->
        Cont t w streamFace ->
          Cont streamFace q regseqFace ->
            Cont regseqFace e realFace ->
              Cont realFace h terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory dyadicFace ∧ UnaryHistory streamFace ∧
                    UnaryHistory regseqFace ∧ UnaryHistory realFace ∧
                      UnaryHistory terminal ∧ Cont u v dyadicFace ∧
                        Cont t w streamFace ∧ Cont streamFace q regseqFace ∧
                          Cont regseqFace e realFace ∧ Cont realFace h terminal ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle terminal pkg ∧
                              hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier uvDyadic twStream streamQRegseq regseqEReal realHTerminal terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed uUnary vUnary uvDyadic
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed tUnary wUnary twStream
  have regseqUnary : UnaryHistory regseqFace :=
    unary_cont_closed streamUnary qUnary streamQRegseq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regseqUnary eUnary regseqEReal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realUnary hUnary realHTerminal
  exact
    ⟨dyadicUnary, streamUnary, regseqUnary, realUnary, terminalUnary, uvDyadic,
      twStream, streamQRegseq, regseqEReal, realHTerminal, pPkg, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
