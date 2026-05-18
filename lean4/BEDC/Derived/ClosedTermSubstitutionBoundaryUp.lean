import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

/-!
# ClosedTermSubstitutionBoundaryUp carrier.
-/

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite closed-substitution boundary packet with the thirteen displayed BEDC rows. -/
inductive ClosedTermSubstitutionBoundaryUp : Type where
  | mk :
      (term value depth sourceClosed valueClosed shiftRow substituteRow ledger audit transport
        route provenance name : BHist) →
      ClosedTermSubstitutionBoundaryUp
  deriving DecidableEq

def closedTermSubstitutionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedTermSubstitutionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedTermSubstitutionBoundaryEncodeBHist h

def closedTermSubstitutionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedTermSubstitutionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedTermSubstitutionBoundaryDecodeBHist tail)

private theorem ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedTermSubstitutionBoundaryDecodeBHist
          (closedTermSubstitutionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedTermSubstitutionBoundaryToEventFlow :
    ClosedTermSubstitutionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedTermSubstitutionBoundaryUp.mk term value depth sourceClosed valueClosed shiftRow
      substituteRow ledger audit transport route provenance name =>
      [[BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist term,
        [BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist value,
        [BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist depth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist sourceClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist valueClosed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist shiftRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist substituteRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionBoundaryEncodeBHist name]

private def closedTermSubstitutionBoundaryDecodePacket
    (term value depth sourceClosed valueClosed shiftRow substituteRow ledger audit transport route
      provenance name : RawEvent) : ClosedTermSubstitutionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ClosedTermSubstitutionBoundaryUp.mk
    (closedTermSubstitutionBoundaryDecodeBHist term)
    (closedTermSubstitutionBoundaryDecodeBHist value)
    (closedTermSubstitutionBoundaryDecodeBHist depth)
    (closedTermSubstitutionBoundaryDecodeBHist sourceClosed)
    (closedTermSubstitutionBoundaryDecodeBHist valueClosed)
    (closedTermSubstitutionBoundaryDecodeBHist shiftRow)
    (closedTermSubstitutionBoundaryDecodeBHist substituteRow)
    (closedTermSubstitutionBoundaryDecodeBHist ledger)
    (closedTermSubstitutionBoundaryDecodeBHist audit)
    (closedTermSubstitutionBoundaryDecodeBHist transport)
    (closedTermSubstitutionBoundaryDecodeBHist route)
    (closedTermSubstitutionBoundaryDecodeBHist provenance)
    (closedTermSubstitutionBoundaryDecodeBHist name)

def closedTermSubstitutionBoundaryFromEventFlow :
    EventFlow → Option ClosedTermSubstitutionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | value :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | depth :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sourceClosed :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | valueClosed :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | shiftRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | substituteRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | audit :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | transport :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | route :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | provenance :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | name :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (closedTermSubstitutionBoundaryDecodePacket
                                                                                                                  term
                                                                                                                  value
                                                                                                                  depth
                                                                                                                  sourceClosed
                                                                                                                  valueClosed
                                                                                                                  shiftRow
                                                                                                                  substituteRow
                                                                                                                  ledger
                                                                                                                  audit
                                                                                                                  transport
                                                                                                                  route
                                                                                                                  provenance
                                                                                                                  name)
                                                                                                          | _ :: _ => none

private theorem ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_round :
    ∀ x : ClosedTermSubstitutionBoundaryUp,
      closedTermSubstitutionBoundaryFromEventFlow
          (closedTermSubstitutionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term value depth sourceClosed valueClosed shiftRow substituteRow ledger audit transport
      route provenance name =>
      change
        some
          (closedTermSubstitutionBoundaryDecodePacket
            (closedTermSubstitutionBoundaryEncodeBHist term)
            (closedTermSubstitutionBoundaryEncodeBHist value)
            (closedTermSubstitutionBoundaryEncodeBHist depth)
            (closedTermSubstitutionBoundaryEncodeBHist sourceClosed)
            (closedTermSubstitutionBoundaryEncodeBHist valueClosed)
            (closedTermSubstitutionBoundaryEncodeBHist shiftRow)
            (closedTermSubstitutionBoundaryEncodeBHist substituteRow)
            (closedTermSubstitutionBoundaryEncodeBHist ledger)
            (closedTermSubstitutionBoundaryEncodeBHist audit)
            (closedTermSubstitutionBoundaryEncodeBHist transport)
            (closedTermSubstitutionBoundaryEncodeBHist route)
            (closedTermSubstitutionBoundaryEncodeBHist provenance)
            (closedTermSubstitutionBoundaryEncodeBHist name)) =
          some
            (ClosedTermSubstitutionBoundaryUp.mk term value depth sourceClosed valueClosed
              shiftRow substituteRow ledger audit transport route provenance name)
      unfold closedTermSubstitutionBoundaryDecodePacket
      have hmk :
          ClosedTermSubstitutionBoundaryUp.mk
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist term))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist value))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist depth))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist sourceClosed))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist valueClosed))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist shiftRow))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist substituteRow))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist ledger))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist audit))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist transport))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist route))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist provenance))
              (closedTermSubstitutionBoundaryDecodeBHist
                (closedTermSubstitutionBoundaryEncodeBHist name)) =
            ClosedTermSubstitutionBoundaryUp.mk term value depth sourceClosed valueClosed
              shiftRow substituteRow ledger audit transport route provenance name := by
        rw [ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode term,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode value,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode depth,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode sourceClosed,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode valueClosed,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode shiftRow,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode substituteRow,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode ledger,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode audit,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode transport,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode route,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode provenance,
          ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode name]
      exact congrArg Option.some hmk

private theorem ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_injective
    {x y : ClosedTermSubstitutionBoundaryUp} :
    closedTermSubstitutionBoundaryToEventFlow x =
        closedTermSubstitutionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedTermSubstitutionBoundaryFromEventFlow
          (closedTermSubstitutionBoundaryToEventFlow x) =
        closedTermSubstitutionBoundaryFromEventFlow
          (closedTermSubstitutionBoundaryToEventFlow y) :=
    congrArg closedTermSubstitutionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_round x).symm
      (Eq.trans hread (ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_round y)))

instance closedTermSubstitutionBoundaryBHistCarrier :
    BHistCarrier ClosedTermSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedTermSubstitutionBoundaryToEventFlow
  fromEventFlow := closedTermSubstitutionBoundaryFromEventFlow

instance closedTermSubstitutionBoundaryChapterTasteGate :
    ChapterTasteGate ClosedTermSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedTermSubstitutionBoundaryFromEventFlow
          (closedTermSubstitutionBoundaryToEventFlow x) =
        some x
    exact ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_injective heq)

theorem ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment :
    closedTermSubstitutionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        closedTermSubstitutionBoundaryDecodeBHist
            (closedTermSubstitutionBoundaryEncodeBHist h) =
          h) ∧
        (∀ x : ClosedTermSubstitutionBoundaryUp,
          closedTermSubstitutionBoundaryFromEventFlow
              (closedTermSubstitutionBoundaryToEventFlow x) =
            some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_decode
    · exact ClosedTermSubstitutionBoundaryPacket_single_carrier_alignment_round

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedTermSubstitutionBoundaryClassifier
    (source value depth shift substitution : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧ UnaryHistory shift ∧
    UnaryHistory substitution ∧ Cont source value shift ∧ Cont shift depth substitution

theorem ClosedTermSubstitutionBoundaryClassifier_component_transport
    {source source' value value' depth depth' shift shift' substitution substitution' : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      hsame source source' ->
        hsame value value' ->
          hsame depth depth' ->
            Cont source' value' shift' ->
              Cont shift' depth' substitution' ->
                ClosedTermSubstitutionBoundaryClassifier source' value' depth' shift'
                    substitution' ∧
                  hsame shift shift' ∧ hsame substitution substitution' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier sameSource sameValue sameDepth sourceValueShift' shiftDepthSubstitution'
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, _substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShift : hsame shift shift' :=
    cont_respects_hsame sameSource sameValue sourceValueShift sourceValueShift'
  have sameSubstitution : hsame substitution substitution' :=
    cont_respects_hsame sameShift sameDepth shiftDepthSubstitution shiftDepthSubstitution'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have valueUnary' : UnaryHistory value' := unary_transport valueUnary sameValue
  have depthUnary' : UnaryHistory depth' := unary_transport depthUnary sameDepth
  have shiftUnary' : UnaryHistory shift' :=
    unary_cont_closed sourceUnary' valueUnary' sourceValueShift'
  have substitutionUnary' : UnaryHistory substitution' :=
    unary_cont_closed shiftUnary' depthUnary' shiftDepthSubstitution'
  exact
    ⟨⟨sourceUnary', valueUnary', depthUnary', shiftUnary', substitutionUnary',
        sourceValueShift', shiftDepthSubstitution'⟩,
      sameShift, sameSubstitution⟩

theorem ClosedTermSubstitutionBoundaryConsumerBoundary [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                  UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                    UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                      Cont source value shift ∧ Cont shift depth substitution ∧
                        Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                          Cont ledger audit route ∧ Cont route audit consumer ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact
    ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary,
      auditUnary, routeUnary, consumerUnary, sourceValueShift, shiftDepthSubstitution,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerPkg⟩

theorem ClosedTermSubstitutionBoundaryNamecertObligations [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    ClosedTermSubstitutionBoundaryClassifier source value depth shift
                      substitution ∧ hsame row consumer)
                  (fun row : BHist => Cont route audit row ∧ PkgSig bundle consumer pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumer pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
  have classifierWitness :
      ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution :=
    classifier
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer
        (And.intro classifierWitness (hsame_refl consumer))
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
      intro row source
      exact And.intro
        (cont_result_hsame_transport routeAuditConsumer (hsame_symm source.right))
        consumerPkg
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport consumerUnary (hsame_symm source.right)) consumerPkg
  }

theorem ClosedTermSubstitutionBoundarySourceClosednessAdmission
    {source value depth shift substitution shiftRead substitutionRead : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          hsame shiftRead shift ∧ hsame substitutionRead substitution ∧ UnaryHistory source ∧
            UnaryHistory shiftRead ∧ UnaryHistory substitutionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, _substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueShiftRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed shiftReadUnary depthUnary shiftReadDepthSubstitutionRead
  exact
    ⟨sameShiftRead, sameSubstitutionRead, sourceUnary, shiftReadUnary,
      substitutionReadUnary⟩

theorem ClosedTermSubstitutionBoundarySubstitutionRowExactness
    {source value depth shift substitution substitutionRead ledger audit : BHist} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift depth substitutionRead ->
        Cont substitutionRead value ledger ->
          Cont ledger depth audit ->
            hsame substitutionRead substitution ∧ UnaryHistory substitutionRead ∧
              UnaryHistory ledger ∧ UnaryHistory audit ∧ Cont substitutionRead value ledger ∧
                Cont ledger depth audit := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier substitutionReadRoute substitutionReadValueLedger ledgerDepthAudit
  obtain ⟨_sourceUnary, valueUnary, depthUnary, shiftUnary, _substitutionUnary,
    _sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_deterministic substitutionReadRoute shiftDepthSubstitution
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed shiftUnary depthUnary substitutionReadRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed substitutionReadUnary valueUnary substitutionReadValueLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed ledgerUnary depthUnary ledgerDepthAudit
  exact
    ⟨sameSubstitutionRead, substitutionReadUnary, ledgerUnary, auditUnary,
      substitutionReadValueLedger, ledgerDepthAudit⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
