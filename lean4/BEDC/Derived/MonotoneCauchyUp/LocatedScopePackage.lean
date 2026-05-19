import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_located_scope_package [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow trapRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg →
      Cont schedule modulus commonWindow →
        Cont ledger interval trapRead →
          Cont commonWindow trapRead locatedRead →
            PkgSig bundle locatedRead pkg →
              UnaryHistory commonWindow ∧ UnaryHistory trapRead ∧
                UnaryHistory locatedRead ∧ Cont schedule modulus commonWindow ∧
                  Cont ledger interval trapRead ∧ Cont commonWindow trapRead locatedRead ∧
                    PkgSig bundle nameRow pkg ∧ PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleModulusCommon ledgerIntervalTrap commonTrapLocated locatedPkg
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed ledgerUnary intervalUnary ledgerIntervalTrap
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed commonWindowUnary trapReadUnary commonTrapLocated
  exact
    ⟨commonWindowUnary, trapReadUnary, locatedReadUnary, scheduleModulusCommon,
      ledgerIntervalTrap, commonTrapLocated, nameRowPkg, locatedPkg⟩

theorem MonotoneCauchyCarrier_carrier_admission_window [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg →
      Cont schedule modulus commonWindow →
        Cont commonWindow interval locatedRead →
          PkgSig bundle locatedRead pkg →
            UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
              UnaryHistory interval ∧ UnaryHistory commonWindow ∧ UnaryHistory locatedRead ∧
                Cont regular schedule modulus ∧ Cont schedule modulus commonWindow ∧
                  Cont commonWindow interval locatedRead ∧ PkgSig bundle nameRow pkg ∧
                    PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleModulusCommon commonIntervalLocated locatedPkg
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed commonWindowUnary intervalUnary commonIntervalLocated
  exact
    ⟨regularUnary, scheduleUnary, modulusUnary, intervalUnary, commonWindowUnary,
      locatedReadUnary, regularScheduleModulus, scheduleModulusCommon, commonIntervalLocated,
      nameRowPkg, locatedPkg⟩

end BEDC.Derived.MonotoneCauchyUp
