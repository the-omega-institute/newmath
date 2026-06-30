import BEDC.Derived.CauchyUp.CoreNameCert

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusReadbackRoute [AskSetup] [PackageSetup]
    {S D R M Q E H C P N streamRead modulusRead compatRead regseqRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCarrier S D R M Q E H C P N bundle pkg ->
      Cont S D streamRead ->
        Cont streamRead M modulusRead ->
          Cont modulusRead Q compatRead ->
            Cont compatRead R regseqRead ->
              Cont regseqRead E sealRead ->
                UnaryHistory streamRead ∧
                  UnaryHistory modulusRead ∧
                    UnaryHistory compatRead ∧
                      UnaryHistory regseqRead ∧
                        UnaryHistory sealRead ∧
                          Cont S D streamRead ∧
                            Cont streamRead M modulusRead ∧
                              Cont modulusRead Q compatRead ∧
                                Cont compatRead R regseqRead ∧
                                  Cont regseqRead E sealRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: CauchyCarrier BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier streamRoute modulusRoute compatRoute regseqRoute sealRoute
  obtain
    ⟨sUnary, dUnary, rUnary, mUnary, qUnary, eUnary, _hUnary, _cUnary, _pUnary,
      _nUnary, packageP, packageN⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary dUnary streamRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed streamUnary mUnary modulusRoute
  have compatUnary : UnaryHistory compatRead :=
    unary_cont_closed modulusUnary qUnary compatRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed compatUnary rUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary eUnary sealRoute
  exact
    ⟨streamUnary, modulusUnary, compatUnary, regseqUnary, sealUnary, streamRoute,
      modulusRoute, compatRoute, regseqRoute, sealRoute, packageP, packageN⟩

end BEDC.Derived.CauchyUp
