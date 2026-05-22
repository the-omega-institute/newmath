import BEDC.Derived.BHistCellRowEmbeddingUp.NameCertObligations
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularVerbRealignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularVerbRealignmentUp : Type where
  | mk
      (sourceVerb orbitRow comparison transport embedding kernelCommitment ledger route
        provenance localName : BHist) :
      CellularVerbRealignmentUp
  deriving DecidableEq

def cellularVerbRealignmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularVerbRealignmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularVerbRealignmentEncodeBHist h

def cellularVerbRealignmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularVerbRealignmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularVerbRealignmentDecodeBHist tail)

private theorem CellularVerbRealignmentTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cellularVerbRealignmentDecodeBHist
        (cellularVerbRealignmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cellularVerbRealignmentToEventFlow :
    CellularVerbRealignmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularVerbRealignmentUp.mk sourceVerb orbitRow comparison transport embedding
      kernelCommitment ledger route provenance localName =>
      [[BMark.b0],
        cellularVerbRealignmentEncodeBHist sourceVerb,
        [BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist orbitRow,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist embedding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist kernelCommitment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularVerbRealignmentEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cellularVerbRealignmentEncodeBHist localName]

def cellularVerbRealignmentFromEventFlow :
    EventFlow → Option CellularVerbRealignmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceVerb :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | orbitRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | comparison :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | embedding :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | kernelCommitment :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] => none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (CellularVerbRealignmentUp.mk
                                                                                          (cellularVerbRealignmentDecodeBHist sourceVerb)
                                                                                          (cellularVerbRealignmentDecodeBHist orbitRow)
                                                                                          (cellularVerbRealignmentDecodeBHist comparison)
                                                                                          (cellularVerbRealignmentDecodeBHist transport)
                                                                                          (cellularVerbRealignmentDecodeBHist embedding)
                                                                                          (cellularVerbRealignmentDecodeBHist kernelCommitment)
                                                                                          (cellularVerbRealignmentDecodeBHist ledger)
                                                                                          (cellularVerbRealignmentDecodeBHist route)
                                                                                          (cellularVerbRealignmentDecodeBHist provenance)
                                                                                          (cellularVerbRealignmentDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem CellularVerbRealignmentTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CellularVerbRealignmentUp,
      cellularVerbRealignmentFromEventFlow
        (cellularVerbRealignmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceVerb orbitRow comparison transport embedding kernelCommitment ledger route
      provenance localName =>
      change
        some
          (CellularVerbRealignmentUp.mk
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist sourceVerb))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist orbitRow))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist comparison))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist transport))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist embedding))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist kernelCommitment))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist ledger))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist route))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist provenance))
            (cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist localName))) =
          some
            (CellularVerbRealignmentUp.mk sourceVerb orbitRow comparison transport embedding
              kernelCommitment ledger route provenance localName)
      rw [CellularVerbRealignmentTasteGate_single_carrier_alignment_decode sourceVerb,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode orbitRow,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode comparison,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode transport,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode embedding,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode kernelCommitment,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode ledger,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode route,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode provenance,
        CellularVerbRealignmentTasteGate_single_carrier_alignment_decode localName]

private theorem CellularVerbRealignmentTasteGate_single_carrier_alignment_injective
    {x y : CellularVerbRealignmentUp} :
    cellularVerbRealignmentToEventFlow x =
      cellularVerbRealignmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularVerbRealignmentFromEventFlow (cellularVerbRealignmentToEventFlow x) =
        cellularVerbRealignmentFromEventFlow (cellularVerbRealignmentToEventFlow y) :=
    congrArg cellularVerbRealignmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CellularVerbRealignmentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CellularVerbRealignmentTasteGate_single_carrier_alignment_round_trip y)))

def cellularVerbRealignmentFields :
    CellularVerbRealignmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularVerbRealignmentUp.mk sourceVerb orbitRow comparison transport embedding
      kernelCommitment ledger route provenance localName =>
      [sourceVerb, orbitRow, comparison, transport, embedding, kernelCommitment, ledger,
        route, provenance, localName]

private theorem CellularVerbRealignmentTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CellularVerbRealignmentUp,
      cellularVerbRealignmentFields x = cellularVerbRealignmentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceVerb1 orbitRow1 comparison1 transport1 embedding1 kernelCommitment1 ledger1
      route1 provenance1 localName1 =>
      cases y with
      | mk sourceVerb2 orbitRow2 comparison2 transport2 embedding2 kernelCommitment2 ledger2
          route2 provenance2 localName2 =>
          cases h
          rfl

instance cellularVerbRealignmentBHistCarrier :
    BHistCarrier CellularVerbRealignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularVerbRealignmentToEventFlow
  fromEventFlow := cellularVerbRealignmentFromEventFlow

instance cellularVerbRealignmentChapterTasteGate :
    ChapterTasteGate CellularVerbRealignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularVerbRealignmentFromEventFlow
        (cellularVerbRealignmentToEventFlow x) = some x
    exact CellularVerbRealignmentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CellularVerbRealignmentTasteGate_single_carrier_alignment_injective heq)

instance cellularVerbRealignmentFieldFaithful :
    FieldFaithful CellularVerbRealignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularVerbRealignmentFields
  field_faithful := CellularVerbRealignmentTasteGate_single_carrier_alignment_field_faithful

instance cellularVerbRealignmentNontrivial :
    Nontrivial CellularVerbRealignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularVerbRealignmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CellularVerbRealignmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularVerbRealignmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularVerbRealignmentChapterTasteGate

theorem CellularVerbRealignmentTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CellularVerbRealignmentUp) ∧
      Nonempty (FieldFaithful CellularVerbRealignmentUp) ∧
        Nonempty (Nontrivial CellularVerbRealignmentUp) ∧
          (∀ h : BHist,
            cellularVerbRealignmentDecodeBHist
              (cellularVerbRealignmentEncodeBHist h) = h) ∧
            (∀ x : CellularVerbRealignmentUp,
              cellularVerbRealignmentFromEventFlow
                (cellularVerbRealignmentToEventFlow x) = some x) ∧
              (∀ x y : CellularVerbRealignmentUp,
                cellularVerbRealignmentToEventFlow x =
                  cellularVerbRealignmentToEventFlow y → x = y) ∧
                cellularVerbRealignmentEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cellularVerbRealignmentChapterTasteGate⟩
  · constructor
    · exact ⟨cellularVerbRealignmentFieldFaithful⟩
    · constructor
      · exact ⟨cellularVerbRealignmentNontrivial⟩
      · constructor
        · exact CellularVerbRealignmentTasteGate_single_carrier_alignment_decode
        · constructor
          · exact CellularVerbRealignmentTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact CellularVerbRealignmentTasteGate_single_carrier_alignment_injective heq
            · rfl

theorem CellularVerbRealignment_embedding_namecert_tastegate_boundary [AskSetup] [PackageSetup]
    {source bitRow width orbitZero readback transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.BHistCellRowEmbeddingUp.BHistCellRowEmbeddingCarrier source bitRow width
        orbitZero readback transports routes provenance name bundle pkg →
      Nonempty (ChapterTasteGate CellularVerbRealignmentUp) ∧
        Nonempty (FieldFaithful CellularVerbRealignmentUp) ∧
          SemanticNameCert
            (fun row : BHist =>
              BEDC.Derived.BHistCellRowEmbeddingUp.BHistCellRowEmbeddingCarrier source bitRow
                  width orbitZero readback transports routes provenance name bundle pkg ∧
                (hsame row source ∨ hsame row bitRow ∨ hsame row width ∨
                  hsame row orbitZero ∨ hsame row readback ∨ hsame row transports ∨
                  hsame row routes ∨ hsame row provenance ∨ hsame row name))
            (fun _row : BHist =>
              Cont source bitRow width ∧ Cont orbitZero readback routes ∧
                PkgSig bundle provenance pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
            hsame := by
  intro embeddingCarrier
  exact
    ⟨⟨cellularVerbRealignmentChapterTasteGate⟩,
      ⟨cellularVerbRealignmentFieldFaithful⟩,
      BEDC.Derived.BHistCellRowEmbeddingUp.BHistCellRowEmbeddingCarrier_namecert_obligations
        embeddingCarrier⟩

end BEDC.Derived.CellularVerbRealignmentUp
