import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapDependencyWeaveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapDependencyWeaveUp : Type where
  | mk (M L O F S H C P N : BHist) : AuditMapDependencyWeaveUp
  deriving DecidableEq

def AuditMapDependencyWeaveCarrier [AskSetup] [PackageSetup]
    (localMap neighbour obstruction frontier synthesis transport continuation provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory localMap ∧ UnaryHistory neighbour ∧ UnaryHistory obstruction ∧
    UnaryHistory frontier ∧ UnaryHistory synthesis ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont localMap neighbour transport ∧ Cont obstruction frontier continuation ∧
          Cont synthesis transport provenance ∧ PkgSig bundle provenance pkg

theorem AuditMapDependencyWeaveRouteAdmission [AskSetup] [PackageSetup]
    {localMap neighbour obstruction frontier synthesis transport continuation provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapDependencyWeaveCarrier localMap neighbour obstruction frontier synthesis transport
        continuation provenance localName bundle pkg →
      Cont continuation localName route →
        PkgSig bundle route pkg →
          UnaryHistory localMap ∧ UnaryHistory neighbour ∧ UnaryHistory obstruction ∧
            UnaryHistory frontier ∧ UnaryHistory synthesis ∧ UnaryHistory route ∧
              Cont continuation localName route ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont routePkg
  rcases carrier with
    ⟨localMapUnary, neighbourUnary, obstructionUnary, frontierUnary, synthesisUnary,
      _transportUnary, continuationUnary, _provenanceUnary, localNameUnary,
      _mapTransport, _obstructionContinuation, _synthesisProvenance, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed continuationUnary localNameUnary routeCont
  exact
    ⟨localMapUnary, neighbourUnary, obstructionUnary, frontierUnary, synthesisUnary,
      routeUnary, routeCont, provenancePkg, routePkg⟩

theorem AuditMapDependencyWeaveObstructionLedger [AskSetup] [PackageSetup]
    {localMap neighbour obstruction frontier synthesis transport continuation provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapDependencyWeaveCarrier localMap neighbour obstruction frontier synthesis transport
        continuation provenance localName bundle pkg →
      Cont continuation localName route →
        PkgSig bundle route pkg →
          UnaryHistory obstruction ∧ UnaryHistory frontier ∧
            Cont obstruction frontier continuation ∧ PkgSig bundle provenance pkg ∧
              UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeCont _routePkg
  rcases carrier with
    ⟨_localMapUnary, _neighbourUnary, obstructionUnary, frontierUnary, _synthesisUnary,
      _transportUnary, continuationUnary, _provenanceUnary, localNameUnary,
      _mapTransport, obstructionContinuation, _synthesisProvenance, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed continuationUnary localNameUnary routeCont
  exact ⟨obstructionUnary, frontierUnary, obstructionContinuation, provenancePkg, routeUnary⟩

def auditMapDependencyWeaveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapDependencyWeaveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapDependencyWeaveEncodeBHist h

def auditMapDependencyWeaveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapDependencyWeaveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapDependencyWeaveDecodeBHist tail)

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMapDependencyWeaveToEventFlow : AuditMapDependencyWeaveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapDependencyWeaveUp.mk M L O F S H C P N =>
      [[BMark.b0],
        auditMapDependencyWeaveEncodeBHist M,
        [BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapDependencyWeaveEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapDependencyWeaveEncodeBHist N]

def auditMapDependencyWeaveFromEventFlow : EventFlow → Option AuditMapDependencyWeaveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restLTag =>
          match restLTag with
          | [] => none
          | _tagL :: restL =>
              match restL with
              | [] => none
              | L :: restOTag =>
                  match restOTag with
                  | [] => none
                  | _tagO :: restO =>
                      match restO with
                      | [] => none
                      | O :: restFTag =>
                          match restFTag with
                          | [] => none
                          | _tagF :: restF =>
                              match restF with
                              | [] => none
                              | F :: restSTag =>
                                  match restSTag with
                                  | [] => none
                                  | _tagS :: restS =>
                                      match restS with
                                      | [] => none
                                      | S :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restCTag =>
                                                  match restCTag with
                                                  | [] => none
                                                  | _tagC :: restC =>
                                                      match restC with
                                                      | [] => none
                                                      | C :: restPTag =>
                                                          match restPTag with
                                                          | [] => none
                                                          | _tagP :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (AuditMapDependencyWeaveUp.mk
                                                                                  (auditMapDependencyWeaveDecodeBHist M)
                                                                                  (auditMapDependencyWeaveDecodeBHist L)
                                                                                  (auditMapDependencyWeaveDecodeBHist O)
                                                                                  (auditMapDependencyWeaveDecodeBHist F)
                                                                                  (auditMapDependencyWeaveDecodeBHist S)
                                                                                  (auditMapDependencyWeaveDecodeBHist H)
                                                                                  (auditMapDependencyWeaveDecodeBHist C)
                                                                                  (auditMapDependencyWeaveDecodeBHist P)
                                                                                  (auditMapDependencyWeaveDecodeBHist N))
                                                                          | _ :: _ => none

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AuditMapDependencyWeaveUp,
      auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L O F S H C P N =>
      change
        some
          (AuditMapDependencyWeaveUp.mk
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist M))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist L))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist O))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist F))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist S))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist H))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist C))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist P))
            (auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist N))) =
          some (AuditMapDependencyWeaveUp.mk M L O F S H C P N)
      rw [AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode M,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode L,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode O,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode F,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode S,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode H,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode C,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode P,
        AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode N]

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective
    {x y : AuditMapDependencyWeaveUp} :
    auditMapDependencyWeaveToEventFlow x = auditMapDependencyWeaveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) =
        auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow y) :=
    congrArg auditMapDependencyWeaveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip y)))

private def auditMapDependencyWeaveFields : AuditMapDependencyWeaveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapDependencyWeaveUp.mk M L O F S H C P N => [M, L, O, F, S, H, C, P, N]

private theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment_fields :
    ∀ x y : AuditMapDependencyWeaveUp,
      auditMapDependencyWeaveFields x = auditMapDependencyWeaveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 L1 O1 F1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 L2 O2 F2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance auditMapDependencyWeaveBHistCarrier :
    BHistCarrier AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapDependencyWeaveToEventFlow
  fromEventFlow := auditMapDependencyWeaveFromEventFlow

instance auditMapDependencyWeaveChapterTasteGate :
    ChapterTasteGate AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x
    exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective heq)

instance auditMapDependencyWeaveFieldFaithful :
    FieldFaithful AuditMapDependencyWeaveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapDependencyWeaveFields
  field_faithful := AuditMapDependencyWeaveTasteGate_single_carrier_alignment_fields

theorem AuditMapDependencyWeaveTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapDependencyWeaveDecodeBHist (auditMapDependencyWeaveEncodeBHist h) = h) ∧
      (∀ x : AuditMapDependencyWeaveUp,
        auditMapDependencyWeaveFromEventFlow (auditMapDependencyWeaveToEventFlow x) = some x) ∧
        (∀ x y : AuditMapDependencyWeaveUp,
          auditMapDependencyWeaveToEventFlow x = auditMapDependencyWeaveToEventFlow y → x = y) ∧
          auditMapDependencyWeaveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_decode
  constructor
  · exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact AuditMapDependencyWeaveTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.AuditMapDependencyWeaveUp
