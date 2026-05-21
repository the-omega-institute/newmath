import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RegularCauchyDifferenceUp finite carrier surface.
-/

namespace BEDC.Derived.RegularCauchyDifferenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyDifferenceCarrier [AskSetup] [PackageSetup]
    (left right schedule tolerance nullConsumer transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory schedule ∧
    UnaryHistory tolerance ∧ UnaryHistory nullConsumer ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont left right schedule ∧ Cont schedule tolerance nullConsumer ∧
          Cont nullConsumer transport route ∧ Cont route localCert provenance ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row localCert)
                (fun row : BHist => hsame row localCert)
                (fun row : BHist => hsame row localCert)
                hsame

theorem RegularCauchyDifferenceCarrier_regularity_closure [AskSetup] [PackageSetup]
    {left right schedule tolerance nullConsumer transport route provenance localCert
      diffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDifferenceCarrier left right schedule tolerance nullConsumer transport route
        provenance localCert bundle pkg ->
      Cont left right schedule ->
        Cont schedule tolerance diffRead ->
          PkgSig bundle provenance pkg ->
            UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory schedule ∧
              UnaryHistory tolerance ∧ UnaryHistory diffRead ∧
                Cont left right schedule ∧ Cont schedule tolerance diffRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier sourceSchedule differenceRead provenancePkg
  obtain ⟨leftUnary, rightUnary, scheduleUnary, toleranceUnary, _nullConsumerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _storedSchedule,
    _storedConsumer, _storedRoute, _storedProvenance, _storedPkg, _nameCert⟩ := carrier
  have diffReadUnary : UnaryHistory diffRead :=
    unary_cont_closed scheduleUnary toleranceUnary differenceRead
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro scheduleUnary
        (And.intro toleranceUnary
          (And.intro diffReadUnary
            (And.intro sourceSchedule
              (And.intro differenceRead provenancePkg))))))

theorem RegularCauchyDifferenceCarrier_tolerance_ledger_exactness [AskSetup] [PackageSetup]
    {left right schedule tolerance nullConsumer transport route provenance localCert
      toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDifferenceCarrier left right schedule tolerance nullConsumer transport route
        provenance localCert bundle pkg ->
      Cont schedule tolerance toleranceRead ->
        UnaryHistory toleranceRead ∧ Cont schedule tolerance toleranceRead ∧
          PkgSig bundle provenance pkg ∧
            SemanticNameCert
              (fun row : BHist => hsame row localCert)
              (fun row : BHist => hsame row localCert)
              (fun row : BHist => hsame row localCert)
              hsame := by
  intro carrier toleranceReadRow
  obtain ⟨_leftUnary, _rightUnary, scheduleUnary, toleranceUnary, _nullConsumerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _storedSchedule,
    _storedConsumer, _storedRoute, _storedProvenance, pkgSig, nameCert⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed scheduleUnary toleranceUnary toleranceReadRow
  exact ⟨toleranceReadUnary, toleranceReadRow, pkgSig, nameCert⟩

theorem RegularCauchyDifferenceCarrier_nullsequence_consumption [AskSetup] [PackageSetup]
    {left right schedule tolerance nullConsumer transport route provenance localCert diffRead
      nullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDifferenceCarrier left right schedule tolerance nullConsumer transport route
        provenance localCert bundle pkg →
      Cont schedule tolerance diffRead →
        Cont diffRead nullConsumer nullRead →
          PkgSig bundle provenance pkg →
            UnaryHistory diffRead ∧ UnaryHistory nullRead ∧
              Cont schedule tolerance diffRead ∧ Cont diffRead nullConsumer nullRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier differenceRead nullConsumerRead provenancePkg
  obtain ⟨_leftUnary, _rightUnary, scheduleUnary, toleranceUnary, nullConsumerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _storedSchedule,
    _storedConsumer, _storedRoute, _storedProvenance, _storedPkg, _nameCert⟩ := carrier
  have diffReadUnary : UnaryHistory diffRead :=
    unary_cont_closed scheduleUnary toleranceUnary differenceRead
  have nullReadUnary : UnaryHistory nullRead :=
    unary_cont_closed diffReadUnary nullConsumerUnary nullConsumerRead
  exact
    ⟨diffReadUnary, nullReadUnary, differenceRead, nullConsumerRead, provenancePkg⟩

end BEDC.Derived.RegularCauchyDifferenceUp
