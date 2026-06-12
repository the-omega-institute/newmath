import BEDC.Derived.DiagonalLimitBudgetUp.CarrierAdmission

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitBudgetScopedRowExhaustion [AskSetup] [PackageSetup]
    {D M W Q E H C P N sealRead replayRead ledgerRead zSeal zLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitBudgetCarrier D M W Q E H C P N bundle pkg →
      Cont W Q sealRead →
        Cont sealRead E replayRead →
          Cont replayRead C ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory Q ∧
                UnaryHistory E ∧ UnaryHistory sealRead ∧ UnaryHistory replayRead ∧
                  UnaryHistory ledgerRead ∧ Cont W Q sealRead ∧
                    Cont sealRead E replayRead ∧ Cont replayRead C ledgerRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle ledgerRead pkg ∧
                        (hsame sealRead (BHist.e0 zSeal) → False) ∧
                          (hsame ledgerRead (BHist.e0 zLedger) → False) := by
  -- BEDC touchpoint anchor: DiagonalLimitBudgetCarrier BHist Cont PkgSig hsame UnaryHistory
  intro carrier sealRoute replayRoute ledgerRoute ledgerPkg
  obtain ⟨dUnary, mUnary, wUnary, qUnary, eUnary, _hUnary, cUnary, _pUnary, _nUnary,
    _windowRoute, _dyadicRoute, provenancePkg, _namePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed wUnary qUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary eUnary replayRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed replayUnary cUnary ledgerRoute
  have sealNoZero : hsame sealRead (BHist.e0 zSeal) → False := by
    intro sameSeal
    exact unary_no_zero_extension (unary_transport sealUnary sameSeal)
  have ledgerNoZero : hsame ledgerRead (BHist.e0 zLedger) → False := by
    intro sameLedger
    exact unary_no_zero_extension (unary_transport ledgerUnary sameLedger)
  exact
    ⟨dUnary, mUnary, wUnary, qUnary, eUnary, sealUnary, replayUnary, ledgerUnary,
      sealRoute, replayRoute, ledgerRoute, provenancePkg, ledgerPkg, sealNoZero,
      ledgerNoZero⟩

end BEDC.Derived.DiagonalLimitBudgetUp
