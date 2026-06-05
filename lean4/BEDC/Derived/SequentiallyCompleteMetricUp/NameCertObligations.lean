import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentiallyCompleteMetricCarrier [AskSetup] [PackageSetup]
    (source streamRow modulus limit lateLedger transport route provenance name acceptance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  UnaryHistory source ∧ UnaryHistory streamRow ∧ UnaryHistory modulus ∧
    UnaryHistory limit ∧ UnaryHistory lateLedger ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        UnaryHistory acceptance ∧ Cont source streamRow route ∧
          Cont route limit acceptance ∧ hsame transport name ∧
            PkgSig bundle acceptance pkg

theorem SequentiallyCompleteMetricNameCertObligations [AskSetup] [PackageSetup]
    {X S M L D H C P N metricRead _sequenceRead modulusRead limitRead distanceRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      Cont X S metricRead ->
        Cont metricRead M modulusRead ->
          Cont modulusRead L limitRead ->
            Cont limitRead D distanceRead ->
              Cont distanceRead C replayRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row replayRead ∧ Cont distanceRead C replayRead)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨
                          hsame row D ∨ Cont distanceRead C replayRead)
                      (fun row : BHist =>
                        hsame row replayRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows _metricRoute _modulusRoute _limitRoute _distanceRoute replayRoute
    provenancePkg namePkg
  cases fieldRows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead (And.intro (hsame_refl replayRead) replayRoute)
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
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

theorem SequentiallyCompleteMetricPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {source streamRow modulus limit lateLedger transport route provenance name acceptance :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier source streamRow modulus limit lateLedger transport
        route provenance name acceptance bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          SequentiallyCompleteMetricCarrier source streamRow modulus limit lateLedger
            transport route provenance name acceptance bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          hsame row source ∨ hsame row streamRow ∨ hsame row modulus ∨
            hsame row limit ∨ hsame row lateLedger ∨ hsame row name)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle acceptance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierProof := carrier
  obtain ⟨_sourceUnary, _streamUnary, _modulusUnary, _limitUnary, _ledgerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, nameUnary, _acceptanceUnary,
    _sourceStreamRoute, _routeLimitAcceptance, _transportName, acceptancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name (And.intro carrierProof (hsame_refl name))
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
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact And.intro (unary_transport nameUnary (hsame_symm source.right)) acceptancePkg
  }

end BEDC.Derived.SequentiallyCompleteMetricUp
