import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICLocalJoinLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICLocalJoinLedgerUp : Type where
  | mk (K A B R S O G H C P N : BHist) : MetaCICLocalJoinLedgerUp
  deriving DecidableEq

def metaCICLocalJoinLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICLocalJoinLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICLocalJoinLedgerEncodeBHist h

def metaCICLocalJoinLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICLocalJoinLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICLocalJoinLedgerDecodeBHist tail)

theorem MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metaCICLocalJoinLedger_mk_congr
    {K K' A A' B B' R R' S S' O O' G G' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hA : A' = A) (hB : B' = B) (hR : R' = R) (hS : S' = S)
    (hO : O' = O) (hG : G' = G) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    MetaCICLocalJoinLedgerUp.mk K' A' B' R' S' O' G' H' C' P' N' =
      MetaCICLocalJoinLedgerUp.mk K A B R S O G H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hA
  cases hB
  cases hR
  cases hS
  cases hO
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def metaCICLocalJoinLedgerFields : MetaCICLocalJoinLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICLocalJoinLedgerUp.mk K A B R S O G H C P N =>
      [K, A, B, R, S, O, G, H, C, P, N]

def metaCICLocalJoinLedgerToEventFlow : MetaCICLocalJoinLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICLocalJoinLedgerUp.mk K A B R S O G H C P N =>
      [[BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist K,
        [BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICLocalJoinLedgerEncodeBHist N]

private def metaCICLocalJoinLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICLocalJoinLedgerEventAtDefault index rest

def metaCICLocalJoinLedgerFromEventFlow (ef : EventFlow) : Option MetaCICLocalJoinLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICLocalJoinLedgerUp.mk
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 1 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 3 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 5 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 7 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 9 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 11 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 13 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 15 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 17 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 19 ef))
      (metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEventAtDefault 21 ef)))

theorem MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICLocalJoinLedgerUp) :
    metaCICLocalJoinLedgerFromEventFlow (metaCICLocalJoinLedgerToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K A B R S O G H C P N =>
      exact
        congrArg some
          (metaCICLocalJoinLedger_mk_congr
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist K)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist A)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist B)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist R)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist S)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist O)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist G)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist H)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist C)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist P)
            (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist N))

theorem MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICLocalJoinLedgerUp} :
    metaCICLocalJoinLedgerToEventFlow x = metaCICLocalJoinLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICLocalJoinLedgerFromEventFlow (metaCICLocalJoinLedgerToEventFlow x) =
        metaCICLocalJoinLedgerFromEventFlow (metaCICLocalJoinLedgerToEventFlow y) :=
    congrArg metaCICLocalJoinLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_round_trip y)))

theorem MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_field_faithful
    (x y : MetaCICLocalJoinLedgerUp) :
    metaCICLocalJoinLedgerFields x = metaCICLocalJoinLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk K A B R S O G H C P N =>
      cases y with
      | mk K' A' B' R' S' O' G' H' C' P' N' =>
          cases hfields
          rfl

instance metaCICLocalJoinLedgerBHistCarrier : BHistCarrier MetaCICLocalJoinLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICLocalJoinLedgerToEventFlow
  fromEventFlow := metaCICLocalJoinLedgerFromEventFlow

instance metaCICLocalJoinLedgerChapterTasteGate : ChapterTasteGate MetaCICLocalJoinLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICLocalJoinLedgerFromEventFlow (metaCICLocalJoinLedgerToEventFlow x) =
        some x
    exact MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metaCICLocalJoinLedgerFieldFaithful : FieldFaithful MetaCICLocalJoinLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICLocalJoinLedgerFields
  field_faithful := MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_field_faithful

instance metaCICLocalJoinLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICLocalJoinLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICLocalJoinLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICLocalJoinLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICLocalJoinLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICLocalJoinLedgerChapterTasteGate

theorem MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICLocalJoinLedgerDecodeBHist (metaCICLocalJoinLedgerEncodeBHist h) = h) ∧
      (forall x : MetaCICLocalJoinLedgerUp,
        metaCICLocalJoinLedgerFromEventFlow (metaCICLocalJoinLedgerToEventFlow x) =
          some x) ∧
        (forall x y : MetaCICLocalJoinLedgerUp,
          metaCICLocalJoinLedgerToEventFlow x = metaCICLocalJoinLedgerToEventFlow y ->
            x = y) ∧
          metaCICLocalJoinLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_decode_encode_bhist,
      MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact
          MetaCICLocalJoinLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
            heq,
      rfl⟩

end BEDC.Derived.MetaCICLocalJoinLedgerUp
