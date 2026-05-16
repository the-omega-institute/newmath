import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_mature_route_summary [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
      Cont interval realSeal sealRead ->
      Cont commonWindow sealRead terminalRead ->
      PkgSig bundle terminalRead pkg ->
        UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
          UnaryHistory ledger ∧ UnaryHistory interval ∧ UnaryHistory realSeal ∧
            UnaryHistory commonWindow ∧ UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧
              Cont regular schedule modulus ∧ Cont schedule modulus commonWindow ∧
                Cont modulus ledger interval ∧ Cont interval realSeal sealRead ∧
                  Cont commonWindow sealRead terminalRead ∧ PkgSig bundle nameRow pkg ∧
                    PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleModulusCommon intervalRealSealRead commonSealTerminal terminalPkg
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed commonWindowUnary sealReadUnary commonSealTerminal
  exact
    ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary, realSealUnary,
      commonWindowUnary, sealReadUnary, terminalReadUnary, regularScheduleModulus,
      scheduleModulusCommon, modulusLedgerInterval, intervalRealSealRead, commonSealTerminal,
      nameRowPkg, terminalPkg⟩

end BEDC.Derived.MonotoneCauchyUp
