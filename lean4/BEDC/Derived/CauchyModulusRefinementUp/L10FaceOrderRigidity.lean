import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementL10FaceOrderRigidity [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n streamFace dyadicFace regSeqFace realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont w q streamFace →
        Cont streamFace t dyadicFace →
          Cont dyadicFace q regSeqFace →
            Cont regSeqFace e realFace →
              PkgSig bundle realFace pkg →
                UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory t ∧ UnaryHistory e ∧
                  UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                    UnaryHistory regSeqFace ∧ UnaryHistory realFace ∧
                      Cont w q streamFace ∧ Cont streamFace t dyadicFace ∧
                        Cont dyadicFace q regSeqFace ∧ Cont regSeqFace e realFace ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier wQStream streamTDyadic dyadicQRegSeq regSeqEReal realPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh,
      pPkg, _hn⟩
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed wUnary qUnary wQStream
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamUnary tUnary streamTDyadic
  have regSeqUnary : UnaryHistory regSeqFace :=
    unary_cont_closed dyadicUnary qUnary dyadicQRegSeq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regSeqUnary eUnary regSeqEReal
  exact
    ⟨wUnary, qUnary, tUnary, eUnary, streamUnary, dyadicUnary, regSeqUnary,
      realUnary, wQStream, streamTDyadic, dyadicQRegSeq, regSeqEReal, pPkg, realPkg⟩

theorem CauchyModulusRefinementCarrier_l10_face_order_rigidity
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n l10Read sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w l10Read ->
        Cont l10Read q sealRead ->
          Cont sealRead e terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory l10Read ∧ UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧
                Cont t w l10Read ∧ Cont l10Read q sealRead ∧
                  Cont sealRead e terminalRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle terminalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier l10Route sealRoute terminalRoute terminalPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩ :=
    carrier
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed tUnary wUnary l10Route
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed l10Unary qUnary sealRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealUnary eUnary terminalRoute
  exact
    ⟨l10Unary, sealUnary, terminalUnary, l10Route, sealRoute, terminalRoute, pPkg,
      terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
