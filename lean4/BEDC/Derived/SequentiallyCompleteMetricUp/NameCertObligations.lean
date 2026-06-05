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
    (source streamRow modulus limit lateLedger transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  UnaryHistory source ∧ UnaryHistory streamRow ∧ UnaryHistory modulus ∧
    UnaryHistory limit ∧ UnaryHistory lateLedger ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont source streamRow route ∧ Cont route limit lateLedger ∧ hsame transport name ∧
          PkgSig bundle provenance pkg

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
    {source streamRow modulus limit lateLedger transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier source streamRow modulus limit lateLedger transport
        route provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          SequentiallyCompleteMetricCarrier source streamRow modulus limit lateLedger
            transport route provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          hsame row source ∨ hsame row streamRow ∨ hsame row modulus ∨
            hsame row limit ∨ hsame row lateLedger ∨ hsame row name)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierProof := carrier
  obtain ⟨_sourceUnary, _streamUnary, _modulusUnary, _limitUnary, _ledgerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, nameUnary, _sourceStreamRoute,
    _routeLimitLedger, _transportName, provenancePkg⟩ := carrier
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
      exact And.intro (unary_transport nameUnary (hsame_symm source.right)) provenancePkg
  }

theorem SequentiallyCompleteMetricRealSealNonescape [AskSetup] [PackageSetup]
    {X S R M L D H C P N windowRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory D →
            UnaryHistory C →
              UnaryHistory N →
                Cont S R windowRead →
                  Cont windowRead D regularRead →
                    Cont regularRead N sealRead →
                      Cont sealRead C namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle namedRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row R ∨ hsame row D ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S R windowRead ∧
                                    Cont windowRead D regularRead ∧
                                      Cont regularRead N sealRead ∧
                                        Cont sealRead C namedRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle namedRead pkg)
                                hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows sUnary rUnary dUnary cUnary nUnary windowRoute regularRoute sealRoute
    namedRoute provenancePkg namedPkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary dUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary nUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R windowRead ∧ Cont windowRead D regularRead ∧
              Cont regularRead N sealRead ∧ Cont sealRead C namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, windowRoute, regularRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
