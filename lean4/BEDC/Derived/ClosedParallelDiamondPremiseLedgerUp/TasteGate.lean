import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedParallelDiamondPremiseLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedParallelDiamondPremiseLedgerUp : Type where
  | mk :
      (parallelSource residualPremise diamondPremise closedStarHandoff closedNormal auditPacket
        parallelAudit transport replay provenance localName : BHist) →
        ClosedParallelDiamondPremiseLedgerUp
  deriving DecidableEq

def closedParallelDiamondPremiseLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedParallelDiamondPremiseLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedParallelDiamondPremiseLedgerEncodeBHist h

def closedParallelDiamondPremiseLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedParallelDiamondPremiseLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedParallelDiamondPremiseLedgerDecodeBHist tail)

private theorem closedParallelDiamondPremiseLedger_decode_encode_bhist :
    ∀ h : BHist, closedParallelDiamondPremiseLedgerDecodeBHist
      (closedParallelDiamondPremiseLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedParallelDiamondPremiseLedgerFields :
    ClosedParallelDiamondPremiseLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedParallelDiamondPremiseLedgerUp.mk parallelSource residualPremise diamondPremise
      closedStarHandoff closedNormal auditPacket parallelAudit transport replay provenance
      localName =>
      [parallelSource, residualPremise, diamondPremise, closedStarHandoff, closedNormal,
        auditPacket, parallelAudit, transport, replay, provenance, localName]

def closedParallelDiamondPremiseLedgerToEventFlow :
    ClosedParallelDiamondPremiseLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (closedParallelDiamondPremiseLedgerFields x).map
        closedParallelDiamondPremiseLedgerEncodeBHist

def closedParallelDiamondPremiseLedgerFromEventFlow :
    EventFlow → Option ClosedParallelDiamondPremiseLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | parallelSource :: residualPremise :: diamondPremise :: closedStarHandoff :: closedNormal ::
      auditPacket :: parallelAudit :: transport :: replay :: provenance :: localName :: [] =>
      some
        (ClosedParallelDiamondPremiseLedgerUp.mk
          (closedParallelDiamondPremiseLedgerDecodeBHist parallelSource)
          (closedParallelDiamondPremiseLedgerDecodeBHist residualPremise)
          (closedParallelDiamondPremiseLedgerDecodeBHist diamondPremise)
          (closedParallelDiamondPremiseLedgerDecodeBHist closedStarHandoff)
          (closedParallelDiamondPremiseLedgerDecodeBHist closedNormal)
          (closedParallelDiamondPremiseLedgerDecodeBHist auditPacket)
          (closedParallelDiamondPremiseLedgerDecodeBHist parallelAudit)
          (closedParallelDiamondPremiseLedgerDecodeBHist transport)
          (closedParallelDiamondPremiseLedgerDecodeBHist replay)
          (closedParallelDiamondPremiseLedgerDecodeBHist provenance)
          (closedParallelDiamondPremiseLedgerDecodeBHist localName))
  | _ => none

private theorem closedParallelDiamondPremiseLedger_round_trip :
    ∀ x : ClosedParallelDiamondPremiseLedgerUp,
      closedParallelDiamondPremiseLedgerFromEventFlow
        (closedParallelDiamondPremiseLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parallelSource residualPremise diamondPremise closedStarHandoff closedNormal auditPacket
      parallelAudit transport replay provenance localName =>
      change
        some
          (ClosedParallelDiamondPremiseLedgerUp.mk
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist parallelSource))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist residualPremise))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist diamondPremise))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist closedStarHandoff))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist closedNormal))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist auditPacket))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist parallelAudit))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist transport))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist replay))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist provenance))
            (closedParallelDiamondPremiseLedgerDecodeBHist
              (closedParallelDiamondPremiseLedgerEncodeBHist localName))) =
          some
            (ClosedParallelDiamondPremiseLedgerUp.mk parallelSource residualPremise
              diamondPremise closedStarHandoff closedNormal auditPacket parallelAudit transport
              replay provenance localName)
      rw [closedParallelDiamondPremiseLedger_decode_encode_bhist parallelSource,
        closedParallelDiamondPremiseLedger_decode_encode_bhist residualPremise,
        closedParallelDiamondPremiseLedger_decode_encode_bhist diamondPremise,
        closedParallelDiamondPremiseLedger_decode_encode_bhist closedStarHandoff,
        closedParallelDiamondPremiseLedger_decode_encode_bhist closedNormal,
        closedParallelDiamondPremiseLedger_decode_encode_bhist auditPacket,
        closedParallelDiamondPremiseLedger_decode_encode_bhist parallelAudit,
        closedParallelDiamondPremiseLedger_decode_encode_bhist transport,
        closedParallelDiamondPremiseLedger_decode_encode_bhist replay,
        closedParallelDiamondPremiseLedger_decode_encode_bhist provenance,
        closedParallelDiamondPremiseLedger_decode_encode_bhist localName]

private theorem closedParallelDiamondPremiseLedgerToEventFlow_injective
    {x y : ClosedParallelDiamondPremiseLedgerUp} :
    closedParallelDiamondPremiseLedgerToEventFlow x =
      closedParallelDiamondPremiseLedgerToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedParallelDiamondPremiseLedgerFromEventFlow
          (closedParallelDiamondPremiseLedgerToEventFlow x) =
        closedParallelDiamondPremiseLedgerFromEventFlow
          (closedParallelDiamondPremiseLedgerToEventFlow y) :=
    congrArg closedParallelDiamondPremiseLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedParallelDiamondPremiseLedger_round_trip x).symm
      (Eq.trans hread (closedParallelDiamondPremiseLedger_round_trip y)))

private theorem closedParallelDiamondPremiseLedger_fields_faithful :
    ∀ x y : ClosedParallelDiamondPremiseLedgerUp,
      closedParallelDiamondPremiseLedgerFields x =
        closedParallelDiamondPremiseLedgerFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk parallelSource₁ residualPremise₁ diamondPremise₁ closedStarHandoff₁ closedNormal₁
      auditPacket₁ parallelAudit₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk parallelSource₂ residualPremise₂ diamondPremise₂ closedStarHandoff₂ closedNormal₂
          auditPacket₂ parallelAudit₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hParallelSource tail0
          injection tail0 with hResidualPremise tail1
          injection tail1 with hDiamondPremise tail2
          injection tail2 with hClosedStarHandoff tail3
          injection tail3 with hClosedNormal tail4
          injection tail4 with hAuditPacket tail5
          injection tail5 with hParallelAudit tail6
          injection tail6 with hTransport tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hParallelSource
          subst hResidualPremise
          subst hDiamondPremise
          subst hClosedStarHandoff
          subst hClosedNormal
          subst hAuditPacket
          subst hParallelAudit
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance closedParallelDiamondPremiseLedgerBHistCarrier :
    BHistCarrier ClosedParallelDiamondPremiseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedParallelDiamondPremiseLedgerToEventFlow
  fromEventFlow := closedParallelDiamondPremiseLedgerFromEventFlow

instance closedParallelDiamondPremiseLedgerChapterTasteGate :
    ChapterTasteGate ClosedParallelDiamondPremiseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedParallelDiamondPremiseLedgerFromEventFlow
      (closedParallelDiamondPremiseLedgerToEventFlow x) = some x
    exact closedParallelDiamondPremiseLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedParallelDiamondPremiseLedgerToEventFlow_injective heq)

instance closedParallelDiamondPremiseLedgerFieldFaithful :
    FieldFaithful ClosedParallelDiamondPremiseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedParallelDiamondPremiseLedgerFields
  field_faithful := closedParallelDiamondPremiseLedger_fields_faithful

instance closedParallelDiamondPremiseLedgerNontrivial :
    Nontrivial ClosedParallelDiamondPremiseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedParallelDiamondPremiseLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ClosedParallelDiamondPremiseLedgerUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedParallelDiamondPremiseLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedParallelDiamondPremiseLedgerChapterTasteGate

end BEDC.Derived.ClosedParallelDiamondPremiseLedgerUp
