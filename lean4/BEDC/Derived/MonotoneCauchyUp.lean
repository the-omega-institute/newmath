import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MonotoneCauchyCarrier [AskSetup] [PackageSetup]
    (regular schedule modulus ledger interval realSeal transportRow route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regular ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
    UnaryHistory ledger ∧ UnaryHistory interval ∧ UnaryHistory realSeal ∧
      UnaryHistory transportRow ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont regular schedule modulus ∧
          Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
            Cont transportRow route provenance ∧ PkgSig bundle nameRow pkg

theorem MonotoneCauchyCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
            provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun _row : BHist =>
          MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
            provenance nameRow bundle pkg ∧ Cont regular schedule modulus ∧
              Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
                Cont transportRow route provenance)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  intro carrier
  have carrierPacket := carrier
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
          transportRouteProvenance⟩
    ledger_sound := by
      intro _row source
      exact ⟨nameRowPkg, source.right⟩
  }

theorem MonotoneCauchyCarrier_located_interval_handoff [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      UnaryHistory interval ∧ UnaryHistory realSeal ∧ hsame interval (append modulus ledger) ∧
        hsame nameRow (append (append modulus ledger) realSeal) ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    _transportRouteProvenance, nameRowPkg⟩ := carrier
  exact
    ⟨intervalUnary, realSealUnary, modulusLedgerInterval, by
      cases intervalRealSealNameRow
      cases modulusLedgerInterval
      rfl, nameRowPkg⟩

end BEDC.Derived.MonotoneCauchyUp
