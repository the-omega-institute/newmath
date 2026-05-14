import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularCarrierEncodingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularCarrierEncodingUp : Type where
  | mk
      (source bitsReadback embedding substrate transport route provenance nameRow : BHist) :
      CellularCarrierEncodingUp
  deriving DecidableEq

def cellularCarrierEncodingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularCarrierEncodingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularCarrierEncodingEncodeBHist h

def cellularCarrierEncodingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularCarrierEncodingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularCarrierEncodingDecodeBHist tail)

private theorem cellularCarrierEncodingDecode_encode_bhist :
    ∀ h : BHist,
      cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cellularCarrierEncoding_mk_congr
    {source source' bitsReadback bitsReadback' embedding embedding' substrate substrate'
      transport transport' route route' provenance provenance' nameRow nameRow' : BHist}
    (hSource : source' = source)
    (hBitsReadback : bitsReadback' = bitsReadback)
    (hEmbedding : embedding' = embedding)
    (hSubstrate : substrate' = substrate)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameRow : nameRow' = nameRow) :
    CellularCarrierEncodingUp.mk source' bitsReadback' embedding' substrate' transport' route'
        provenance' nameRow' =
      CellularCarrierEncodingUp.mk source bitsReadback embedding substrate transport route
        provenance nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hBitsReadback
  cases hEmbedding
  cases hSubstrate
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameRow
  rfl

def cellularCarrierEncodingToEventFlow : CellularCarrierEncodingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CellularCarrierEncodingUp.mk source bitsReadback embedding substrate transport route
      provenance nameRow =>
      [[BMark.b0],
        cellularCarrierEncodingEncodeBHist source,
        [BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist bitsReadback,
        [BMark.b1, BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist embedding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cellularCarrierEncodingEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cellularCarrierEncodingEncodeBHist nameRow]

private def cellularCarrierEncodingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cellularCarrierEncodingEventAtDefault index rest

def cellularCarrierEncodingFromEventFlow
    (ef : EventFlow) : Option CellularCarrierEncodingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CellularCarrierEncodingUp.mk
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 1 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 3 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 5 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 7 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 9 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 11 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 13 ef))
      (cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEventAtDefault 15 ef)))

private theorem cellularCarrierEncoding_round_trip :
    ∀ x : CellularCarrierEncodingUp,
      cellularCarrierEncodingFromEventFlow (cellularCarrierEncodingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bitsReadback embedding substrate transport route provenance nameRow =>
      change
        some
          (CellularCarrierEncodingUp.mk
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist source))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist bitsReadback))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist embedding))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist substrate))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist transport))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist route))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist provenance))
            (cellularCarrierEncodingDecodeBHist
              (cellularCarrierEncodingEncodeBHist nameRow))) =
          some
            (CellularCarrierEncodingUp.mk source bitsReadback embedding substrate transport
              route provenance nameRow)
      exact
        congrArg some
          (cellularCarrierEncoding_mk_congr
            (cellularCarrierEncodingDecode_encode_bhist source)
            (cellularCarrierEncodingDecode_encode_bhist bitsReadback)
            (cellularCarrierEncodingDecode_encode_bhist embedding)
            (cellularCarrierEncodingDecode_encode_bhist substrate)
            (cellularCarrierEncodingDecode_encode_bhist transport)
            (cellularCarrierEncodingDecode_encode_bhist route)
            (cellularCarrierEncodingDecode_encode_bhist provenance)
            (cellularCarrierEncodingDecode_encode_bhist nameRow))

private theorem cellularCarrierEncodingToEventFlow_injective
    {x y : CellularCarrierEncodingUp} :
    cellularCarrierEncodingToEventFlow x = cellularCarrierEncodingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cellularCarrierEncodingFromEventFlow (cellularCarrierEncodingToEventFlow x) =
        cellularCarrierEncodingFromEventFlow (cellularCarrierEncodingToEventFlow y) :=
    congrArg cellularCarrierEncodingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cellularCarrierEncoding_round_trip x).symm
      (Eq.trans hread (cellularCarrierEncoding_round_trip y)))

instance cellularCarrierEncodingBHistCarrier : BHistCarrier CellularCarrierEncodingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularCarrierEncodingToEventFlow
  fromEventFlow := cellularCarrierEncodingFromEventFlow

instance cellularCarrierEncodingChapterTasteGate :
    ChapterTasteGate CellularCarrierEncodingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cellularCarrierEncodingFromEventFlow
      (cellularCarrierEncodingToEventFlow x) = some x
    exact cellularCarrierEncoding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cellularCarrierEncodingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CellularCarrierEncodingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularCarrierEncodingChapterTasteGate

instance cellularCarrierEncodingFieldFaithful : FieldFaithful CellularCarrierEncodingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CellularCarrierEncodingUp.mk source bitsReadback embedding substrate transport route
        provenance nameRow =>
        [source, bitsReadback, embedding, substrate, transport, route, provenance, nameRow]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ bitsReadback₁ embedding₁ substrate₁ transport₁ route₁ provenance₁ nameRow₁ =>
        cases y with
        | mk source₂ bitsReadback₂ embedding₂ substrate₂ transport₂ route₂ provenance₂ nameRow₂ =>
            injection h with hSource hRest₁
            injection hRest₁ with hBitsReadback hRest₂
            injection hRest₂ with hEmbedding hRest₃
            injection hRest₃ with hSubstrate hRest₄
            injection hRest₄ with hTransport hRest₅
            injection hRest₅ with hRoute hRest₆
            injection hRest₆ with hProvenance hRest₇
            injection hRest₇ with hNameRow _
            cases hSource
            cases hBitsReadback
            cases hEmbedding
            cases hSubstrate
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hNameRow
            rfl

instance cellularCarrierEncodingNontrivial : Nontrivial CellularCarrierEncodingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularCarrierEncodingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CellularCarrierEncodingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CellularCarrierEncodingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cellularCarrierEncodingDecodeBHist (cellularCarrierEncodingEncodeBHist h) = h) ∧
      (∀ x : CellularCarrierEncodingUp,
        cellularCarrierEncodingFromEventFlow (cellularCarrierEncodingToEventFlow x) =
          some x) ∧
      (∀ x y : CellularCarrierEncodingUp,
        cellularCarrierEncodingToEventFlow x = cellularCarrierEncodingToEventFlow y →
          x = y) ∧
      FieldFaithful.fields (X := CellularCarrierEncodingUp)
          (CellularCarrierEncodingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cellularCarrierEncodingDecode_encode_bhist
  · constructor
    · exact cellularCarrierEncoding_round_trip
    · constructor
      · intro x y heq
        exact cellularCarrierEncodingToEventFlow_injective heq
      · rfl

end BEDC.Derived.CellularCarrierEncodingUp
