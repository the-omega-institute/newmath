import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservationConservationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObservationConservationLedgerCarrier [AskSetup] [PackageSetup]
    (oldState newState oldRecords newRecords admission gap transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  UnaryHistory oldState ∧ UnaryHistory newState ∧ UnaryHistory oldRecords ∧
    UnaryHistory newRecords ∧ UnaryHistory admission ∧ UnaryHistory gap ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont oldRecords admission newRecords ∧
          Cont newRecords route newRecords ∧ Cont oldState transport newState ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem ObservationConservationLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {oldState newState oldRecords newRecords admission gap transport route provenance name
      read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationConservationLedgerCarrier oldState newState oldRecords newRecords admission gap
        transport route provenance name bundle pkg →
      Cont oldRecords admission newRecords →
        Cont newRecords route read →
          PkgSig bundle read pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ObservationConservationLedgerCarrier oldState newState oldRecords newRecords
                      admission gap transport route provenance name bundle pkg ∧
                    hsame row newRecords)
                (fun row : BHist =>
                  Cont oldRecords admission newRecords ∧ Cont newRecords route row ∧
                    PkgSig bundle read pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle read pkg)
                hsame ∧
              UnaryHistory oldRecords ∧ UnaryHistory newRecords ∧ UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier oldAdmissionNew newRouteRead readPkg
  have carrierWitness := carrier
  obtain ⟨_oldStateUnary, _newStateUnary, oldRecordsUnary, newRecordsUnary,
    _admissionUnary, _gapUnary, _transportUnary, routeUnary, _provenanceUnary,
    _nameUnary, _carrierAdmission, carrierSelfRoute, _stateTransport, _provenancePkg,
    _namePkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed newRecordsUnary routeUnary newRouteRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ObservationConservationLedgerCarrier oldState newState oldRecords newRecords
                admission gap transport route provenance name bundle pkg ∧
              hsame row newRecords)
          (fun row : BHist =>
            Cont oldRecords admission newRecords ∧ Cont newRecords route row ∧
              PkgSig bundle read pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle read pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro newRecords (And.intro carrierWitness (hsame_refl newRecords))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
      }
      pattern_sound := by
        intro row source
        exact
          And.intro oldAdmissionNew
            (And.intro
              (cont_result_hsame_transport carrierSelfRoute (hsame_symm source.right))
              readPkg)
      ledger_sound := by
        intro row source
        exact
          And.intro (unary_transport newRecordsUnary (hsame_symm source.right)) readPkg
    }
  exact And.intro cert (And.intro oldRecordsUnary (And.intro newRecordsUnary readUnary))

end BEDC.Derived.ObservationConservationLedgerUp
