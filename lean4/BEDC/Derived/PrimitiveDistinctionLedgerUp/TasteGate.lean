import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimitiveDistinctionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimitiveDistinctionLedgerUp : Type where
  | mk : (Z O D T R H C P N : BHist) -> PrimitiveDistinctionLedgerUp
  deriving DecidableEq

def primitiveDistinctionLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primitiveDistinctionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primitiveDistinctionLedgerEncodeBHist h

def primitiveDistinctionLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primitiveDistinctionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primitiveDistinctionLedgerDecodeBHist tail)

private theorem primitiveDistinctionLedger_decode_encode_bhist :
    forall h : BHist,
      primitiveDistinctionLedgerDecodeBHist
        (primitiveDistinctionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def primitiveDistinctionLedgerFields :
    PrimitiveDistinctionLedgerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N =>
      [Z, O, D, T, R, H, C, P, N]

def primitiveDistinctionLedgerToEventFlow :
    PrimitiveDistinctionLedgerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map primitiveDistinctionLedgerEncodeBHist
      (primitiveDistinctionLedgerFields x)

private def primitiveDistinctionLedgerEventHead : EventFlow -> Option RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | row :: _ => some row

private def primitiveDistinctionLedgerEventTail : EventFlow -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => []
  | _ :: tail => tail

private def primitiveDistinctionLedgerEventNil : EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | [] => true
  | _ :: _ => false

private def primitiveDistinctionLedgerBuildFromRows :
    Option RawEvent -> Option RawEvent -> Option RawEvent -> Option RawEvent ->
      Option RawEvent -> Option RawEvent -> Option RawEvent -> Option RawEvent ->
        Option RawEvent -> Option PrimitiveDistinctionLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | z, o, d, t, r, h, c, p, n =>
      match z with
      | none => none
      | some Z =>
          match o with
          | none => none
          | some O =>
              match d with
              | none => none
              | some D =>
                  match t with
                  | none => none
                  | some T =>
                      match r with
                      | none => none
                      | some R =>
                          match h with
                          | none => none
                          | some H =>
                              match c with
                              | none => none
                              | some C =>
                                  match p with
                                  | none => none
                                  | some P =>
                                      match n with
                                      | none => none
                                      | some N =>
                                          some
                                            (PrimitiveDistinctionLedgerUp.mk
                                              (primitiveDistinctionLedgerDecodeBHist Z)
                                              (primitiveDistinctionLedgerDecodeBHist O)
                                              (primitiveDistinctionLedgerDecodeBHist D)
                                              (primitiveDistinctionLedgerDecodeBHist T)
                                              (primitiveDistinctionLedgerDecodeBHist R)
                                              (primitiveDistinctionLedgerDecodeBHist H)
                                              (primitiveDistinctionLedgerDecodeBHist C)
                                              (primitiveDistinctionLedgerDecodeBHist P)
                                              (primitiveDistinctionLedgerDecodeBHist N))

def primitiveDistinctionLedgerFromEventFlow :
    EventFlow -> Option PrimitiveDistinctionLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | rows =>
      let rows1 := primitiveDistinctionLedgerEventTail rows
      let rows2 := primitiveDistinctionLedgerEventTail rows1
      let rows3 := primitiveDistinctionLedgerEventTail rows2
      let rows4 := primitiveDistinctionLedgerEventTail rows3
      let rows5 := primitiveDistinctionLedgerEventTail rows4
      let rows6 := primitiveDistinctionLedgerEventTail rows5
      let rows7 := primitiveDistinctionLedgerEventTail rows6
      let rows8 := primitiveDistinctionLedgerEventTail rows7
      let rows9 := primitiveDistinctionLedgerEventTail rows8
      if primitiveDistinctionLedgerEventNil rows9 then
        primitiveDistinctionLedgerBuildFromRows
          (primitiveDistinctionLedgerEventHead rows)
          (primitiveDistinctionLedgerEventHead rows1)
          (primitiveDistinctionLedgerEventHead rows2)
          (primitiveDistinctionLedgerEventHead rows3)
          (primitiveDistinctionLedgerEventHead rows4)
          (primitiveDistinctionLedgerEventHead rows5)
          (primitiveDistinctionLedgerEventHead rows6)
          (primitiveDistinctionLedgerEventHead rows7)
          (primitiveDistinctionLedgerEventHead rows8)
      else
        none

private theorem primitiveDistinctionLedger_round_trip :
    forall x : PrimitiveDistinctionLedgerUp,
      primitiveDistinctionLedgerFromEventFlow
        (primitiveDistinctionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Z O D T R H C P N =>
      change
        some
          (PrimitiveDistinctionLedgerUp.mk
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist Z))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist O))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist D))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist T))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist R))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist H))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist C))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist P))
            (primitiveDistinctionLedgerDecodeBHist
              (primitiveDistinctionLedgerEncodeBHist N))) =
          some (PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N)
      simp only [primitiveDistinctionLedger_decode_encode_bhist]

private theorem primitiveDistinctionLedgerToEventFlow_injective
    {x y : PrimitiveDistinctionLedgerUp} :
    primitiveDistinctionLedgerToEventFlow x =
        primitiveDistinctionLedgerToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primitiveDistinctionLedgerFromEventFlow
          (primitiveDistinctionLedgerToEventFlow x) =
        primitiveDistinctionLedgerFromEventFlow
          (primitiveDistinctionLedgerToEventFlow y) :=
    congrArg primitiveDistinctionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (primitiveDistinctionLedger_round_trip x).symm
      (Eq.trans hread (primitiveDistinctionLedger_round_trip y)))

private theorem primitiveDistinctionLedger_field_faithful :
    forall x y : PrimitiveDistinctionLedgerUp,
      primitiveDistinctionLedgerFields x = primitiveDistinctionLedgerFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Z1 O1 D1 T1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk Z2 O2 D2 T2 R2 H2 C2 P2 N2 =>
          cases h
          rfl

instance primitiveDistinctionLedgerBHistCarrier :
    BHistCarrier PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primitiveDistinctionLedgerToEventFlow
  fromEventFlow := primitiveDistinctionLedgerFromEventFlow

instance primitiveDistinctionLedgerChapterTasteGate :
    ChapterTasteGate PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      primitiveDistinctionLedgerFromEventFlow
        (primitiveDistinctionLedgerToEventFlow x) = some x
    exact primitiveDistinctionLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (primitiveDistinctionLedgerToEventFlow_injective heq)

instance primitiveDistinctionLedgerFieldFaithful :
    FieldFaithful PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := primitiveDistinctionLedgerFields
  field_faithful := primitiveDistinctionLedger_field_faithful

instance primitiveDistinctionLedgerNontrivial :
    Nontrivial PrimitiveDistinctionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrimitiveDistinctionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrimitiveDistinctionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PrimitiveDistinctionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primitiveDistinctionLedgerChapterTasteGate

theorem PrimitiveDistinctionLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      primitiveDistinctionLedgerDecodeBHist
        (primitiveDistinctionLedgerEncodeBHist h) = h) /\
      (forall x : PrimitiveDistinctionLedgerUp,
        primitiveDistinctionLedgerFromEventFlow
          (primitiveDistinctionLedgerToEventFlow x) = some x) /\
        (forall x y : PrimitiveDistinctionLedgerUp,
          primitiveDistinctionLedgerToEventFlow x =
              primitiveDistinctionLedgerToEventFlow y ->
            x = y) /\
          primitiveDistinctionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk Z O D T R H C P N =>
          change
            some
              (PrimitiveDistinctionLedgerUp.mk
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist Z))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist O))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist D))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist T))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist R))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist H))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist C))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist P))
                (primitiveDistinctionLedgerDecodeBHist
                  (primitiveDistinctionLedgerEncodeBHist N))) =
              some (PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N)
          rw [primitiveDistinctionLedger_decode_encode_bhist Z,
            primitiveDistinctionLedger_decode_encode_bhist O,
            primitiveDistinctionLedger_decode_encode_bhist D,
            primitiveDistinctionLedger_decode_encode_bhist T,
            primitiveDistinctionLedger_decode_encode_bhist R,
            primitiveDistinctionLedger_decode_encode_bhist H,
            primitiveDistinctionLedger_decode_encode_bhist C,
            primitiveDistinctionLedger_decode_encode_bhist P,
            primitiveDistinctionLedger_decode_encode_bhist N]
    · constructor
      · intro x y heq
        have hread :
            primitiveDistinctionLedgerFromEventFlow
                (primitiveDistinctionLedgerToEventFlow x) =
              primitiveDistinctionLedgerFromEventFlow
                (primitiveDistinctionLedgerToEventFlow y) :=
          congrArg primitiveDistinctionLedgerFromEventFlow heq
        have hx :
            primitiveDistinctionLedgerFromEventFlow
              (primitiveDistinctionLedgerToEventFlow x) = some x := by
          cases x with
          | mk Z O D T R H C P N =>
              change
                some
                  (PrimitiveDistinctionLedgerUp.mk
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist Z))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist O))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist D))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist T))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist R))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist H))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist C))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist P))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist N))) =
                  some (PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N)
              rw [primitiveDistinctionLedger_decode_encode_bhist Z,
                primitiveDistinctionLedger_decode_encode_bhist O,
                primitiveDistinctionLedger_decode_encode_bhist D,
                primitiveDistinctionLedger_decode_encode_bhist T,
                primitiveDistinctionLedger_decode_encode_bhist R,
                primitiveDistinctionLedger_decode_encode_bhist H,
                primitiveDistinctionLedger_decode_encode_bhist C,
                primitiveDistinctionLedger_decode_encode_bhist P,
                primitiveDistinctionLedger_decode_encode_bhist N]
        have hy :
            primitiveDistinctionLedgerFromEventFlow
              (primitiveDistinctionLedgerToEventFlow y) = some y := by
          cases y with
          | mk Z O D T R H C P N =>
              change
                some
                  (PrimitiveDistinctionLedgerUp.mk
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist Z))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist O))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist D))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist T))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist R))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist H))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist C))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist P))
                    (primitiveDistinctionLedgerDecodeBHist
                      (primitiveDistinctionLedgerEncodeBHist N))) =
                  some (PrimitiveDistinctionLedgerUp.mk Z O D T R H C P N)
              rw [primitiveDistinctionLedger_decode_encode_bhist Z,
                primitiveDistinctionLedger_decode_encode_bhist O,
                primitiveDistinctionLedger_decode_encode_bhist D,
                primitiveDistinctionLedger_decode_encode_bhist T,
                primitiveDistinctionLedger_decode_encode_bhist R,
                primitiveDistinctionLedger_decode_encode_bhist H,
                primitiveDistinctionLedger_decode_encode_bhist C,
                primitiveDistinctionLedger_decode_encode_bhist P,
                primitiveDistinctionLedger_decode_encode_bhist N]
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · rfl

end BEDC.Derived.PrimitiveDistinctionLedgerUp
