import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailAgreementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailAgreementCarrier [AskSetup] [PackageSetup]
    (X Y S D A R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory S ∧ UnaryHistory D ∧
    UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
      Cont X Y S ∧ Cont S D A ∧ Cont A R H ∧ Cont H C N ∧
        PkgSig bundle P pkg

theorem RegularCauchyTailAgreementLedgerNonescape [AskSetup] [PackageSetup]
    {X Y S D A R H C P N ledgerRead agreementRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailAgreementCarrier X Y S D A R H C P N bundle pkg ->
      Cont S D ledgerRead ->
        Cont ledgerRead A agreementRead ->
          Cont agreementRead R realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory ledgerRead ∧
                UnaryHistory agreementRead ∧ UnaryHistory realRead ∧ Cont S D ledgerRead ∧
                  Cont ledgerRead A agreementRead ∧ Cont agreementRead R realRead ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier scheduleLedger ledgerAgreement agreementReal realPkg
  obtain ⟨_xUnary, _yUnary, sUnary, dUnary, aUnary, rUnary, _hUnary, _cUnary,
    _sourceSchedule, _scheduleAgreement, _agreementHandoff, _nameRoute, _pkgRow⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sUnary dUnary scheduleLedger
  have agreementUnary : UnaryHistory agreementRead :=
    unary_cont_closed ledgerUnary aUnary ledgerAgreement
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed agreementUnary rUnary agreementReal
  exact
    ⟨sUnary, dUnary, aUnary, ledgerUnary, agreementUnary, realUnary, scheduleLedger,
      ledgerAgreement, agreementReal, realPkg⟩

end BEDC.Derived.RegularCauchyTailAgreementUp
