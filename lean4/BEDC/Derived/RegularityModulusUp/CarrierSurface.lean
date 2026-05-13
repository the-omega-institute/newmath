import BEDC.Derived.RegularityModulusUp

namespace BEDC.Derived.RegularityModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure RegularityModulusDyadicWindowCarrier [AskSetup] [PackageSetup] where
  precision : BHist
  modulus : BHist
  window : BHist
  transport : BHist
  ledger : BHist
  provenance : BHist
  nameRow : BHist
  bundle : ProbeBundle ProbeName
  pkg : Pkg
  precision_unary : UnaryHistory precision
  modulus_unary : UnaryHistory modulus
  window_unary : UnaryHistory window
  name_unary : UnaryHistory nameRow
  precision_window_transport : Cont precision window transport
  transport_modulus_ledger : Cont transport modulus ledger
  ledger_name_provenance : Cont ledger nameRow provenance
  provenance_pkg : PkgSig bundle provenance pkg

theorem RegularityModulusDyadicWindowCarrier_seed_obligation_surface [AskSetup] [PackageSetup]
    (carrier : RegularityModulusDyadicWindowCarrier) :
    RegularityModulusPacket carrier.precision carrier.modulus carrier.window carrier.transport
        carrier.ledger carrier.provenance carrier.nameRow carrier.bundle carrier.pkg ∧
      UnaryHistory carrier.transport ∧ UnaryHistory carrier.ledger ∧
        UnaryHistory carrier.provenance ∧
          SemanticNameCert
            (fun row : BHist => hsame row carrier.provenance ∧ UnaryHistory row ∧
              PkgSig carrier.bundle row carrier.pkg)
            (fun row : BHist => UnaryHistory carrier.precision ∧
              UnaryHistory carrier.modulus ∧ UnaryHistory carrier.window ∧
                Cont carrier.ledger carrier.nameRow row)
            (fun row : BHist => PkgSig carrier.bundle row carrier.pkg ∧
              Cont carrier.precision carrier.window carrier.transport ∧
                Cont carrier.transport carrier.modulus carrier.ledger)
            hsame := by
  -- BEDC touchpoint anchor: BHist RegularityModulusPacket SemanticNameCert
  let transportUnary : UnaryHistory carrier.transport :=
    unary_cont_closed carrier.precision_unary carrier.window_unary
      carrier.precision_window_transport
  let ledgerUnary : UnaryHistory carrier.ledger :=
    unary_cont_closed transportUnary carrier.modulus_unary carrier.transport_modulus_ledger
  let provenanceUnary : UnaryHistory carrier.provenance :=
    unary_cont_closed ledgerUnary carrier.name_unary carrier.ledger_name_provenance
  let packet :
      RegularityModulusPacket carrier.precision carrier.modulus carrier.window carrier.transport
        carrier.ledger carrier.provenance carrier.nameRow carrier.bundle carrier.pkg :=
    ⟨carrier.precision_unary, carrier.modulus_unary, carrier.window_unary,
      carrier.name_unary, carrier.precision_window_transport,
      carrier.transport_modulus_ledger, carrier.ledger_name_provenance,
      carrier.provenance_pkg⟩
  let cert :
      SemanticNameCert
        (fun row : BHist => hsame row carrier.provenance ∧ UnaryHistory row ∧
          PkgSig carrier.bundle row carrier.pkg)
        (fun row : BHist => UnaryHistory carrier.precision ∧
          UnaryHistory carrier.modulus ∧ UnaryHistory carrier.window ∧
            Cont carrier.ledger carrier.nameRow row)
        (fun row : BHist => PkgSig carrier.bundle row carrier.pkg ∧
          Cont carrier.precision carrier.window carrier.transport ∧
            Cont carrier.transport carrier.modulus carrier.ledger)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro carrier.provenance
          ⟨hsame_refl carrier.provenance, provenanceUnary, carrier.provenance_pkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨carrier.precision_unary, carrier.modulus_unary, carrier.window_unary,
          cont_result_hsame_transport carrier.ledger_name_provenance
            (hsame_symm sourceRow.left)⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact
        ⟨carrier.provenance_pkg, carrier.precision_window_transport,
          carrier.transport_modulus_ledger⟩
  }
  exact ⟨packet, transportUnary, ledgerUnary, provenanceUnary, cert⟩

end BEDC.Derived.RegularityModulusUp
