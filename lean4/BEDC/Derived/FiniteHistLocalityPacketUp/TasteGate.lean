import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteHistLocalityPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteHistLocalityPacketUp : Type where
  | mk :
      (H0 H1 L I S T C Q N : BHist) →
      FiniteHistLocalityPacketUp
  deriving DecidableEq

def finiteHistLocalityPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteHistLocalityPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteHistLocalityPacketEncodeBHist h

def finiteHistLocalityPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteHistLocalityPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteHistLocalityPacketDecodeBHist tail)

private theorem finiteHistLocalityPacket_decode_encode_bhist :
    ∀ h : BHist,
      finiteHistLocalityPacketDecodeBHist (finiteHistLocalityPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteHistLocalityPacketFields : FiniteHistLocalityPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N =>
      [H0, H1, L, I, S, T, C, Q, N]

def finiteHistLocalityPacketToEventFlow : FiniteHistLocalityPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        finiteHistLocalityPacketEncodeBHist H0,
        finiteHistLocalityPacketEncodeBHist H1,
        finiteHistLocalityPacketEncodeBHist L,
        finiteHistLocalityPacketEncodeBHist I,
        finiteHistLocalityPacketEncodeBHist S,
        finiteHistLocalityPacketEncodeBHist T,
        finiteHistLocalityPacketEncodeBHist C,
        finiteHistLocalityPacketEncodeBHist Q,
        finiteHistLocalityPacketEncodeBHist N]

def finiteHistLocalityPacketFromEventFlow :
    EventFlow → Option FiniteHistLocalityPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b0, BMark.b1], H0, H1, L, I, S, T, C, Q, N] =>
      some
        (FiniteHistLocalityPacketUp.mk
          (finiteHistLocalityPacketDecodeBHist H0)
          (finiteHistLocalityPacketDecodeBHist H1)
          (finiteHistLocalityPacketDecodeBHist L)
          (finiteHistLocalityPacketDecodeBHist I)
          (finiteHistLocalityPacketDecodeBHist S)
          (finiteHistLocalityPacketDecodeBHist T)
          (finiteHistLocalityPacketDecodeBHist C)
          (finiteHistLocalityPacketDecodeBHist Q)
          (finiteHistLocalityPacketDecodeBHist N))
  | _ => none

private theorem finiteHistLocalityPacket_round_trip :
    ∀ x : FiniteHistLocalityPacketUp,
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H0 H1 L I S T C Q N =>
      change
        some
          (FiniteHistLocalityPacketUp.mk
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist H0))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist H1))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist L))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist I))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist S))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist T))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist C))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist Q))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist N))) =
          some (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N)
      rw [finiteHistLocalityPacket_decode_encode_bhist H0,
        finiteHistLocalityPacket_decode_encode_bhist H1,
        finiteHistLocalityPacket_decode_encode_bhist L,
        finiteHistLocalityPacket_decode_encode_bhist I,
        finiteHistLocalityPacket_decode_encode_bhist S,
        finiteHistLocalityPacket_decode_encode_bhist T,
        finiteHistLocalityPacket_decode_encode_bhist C,
        finiteHistLocalityPacket_decode_encode_bhist Q,
        finiteHistLocalityPacket_decode_encode_bhist N]

private theorem finiteHistLocalityPacketToEventFlow_injective
    {x y : FiniteHistLocalityPacketUp} :
    finiteHistLocalityPacketToEventFlow x = finiteHistLocalityPacketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow y) :=
    congrArg finiteHistLocalityPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteHistLocalityPacket_round_trip x).symm
      (Eq.trans hread (finiteHistLocalityPacket_round_trip y)))

private theorem finiteHistLocalityPacket_field_faithful :
    ∀ x y : FiniteHistLocalityPacketUp,
      finiteHistLocalityPacketFields x = finiteHistLocalityPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H0a H1a La Ia Sa Ta Ca Qa Na =>
      cases y with
      | mk H0b H1b Lb Ib Sb Tb Cb Qb Nb =>
          injection hfields with hH0 t1
          injection t1 with hH1 t2
          injection t2 with hL t3
          injection t3 with hI t4
          injection t4 with hS t5
          injection t5 with hT t6
          injection t6 with hC t7
          injection t7 with hQ t8
          injection t8 with hN _
          cases hH0
          cases hH1
          cases hL
          cases hI
          cases hS
          cases hT
          cases hC
          cases hQ
          cases hN
          rfl

instance finiteHistLocalityPacketBHistCarrier :
    BHistCarrier FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteHistLocalityPacketToEventFlow
  fromEventFlow := finiteHistLocalityPacketFromEventFlow

instance finiteHistLocalityPacketChapterTasteGate :
    ChapterTasteGate FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        some x
    exact finiteHistLocalityPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteHistLocalityPacketToEventFlow_injective heq)

instance finiteHistLocalityPacketFieldFaithful :
    FieldFaithful FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteHistLocalityPacketFields
  field_faithful := finiteHistLocalityPacket_field_faithful

instance finiteHistLocalityPacketNontrivial :
    Nontrivial FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteHistLocalityPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteHistLocalityPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteHistLocalityPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteHistLocalityPacketChapterTasteGate

theorem FiniteHistLocalityPacketTasteGate_single_carrier_alignment :
    forall H0 H1 L I S T C Q N : BHist,
      finiteHistLocalityPacketToEventFlow
          (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
        [[BMark.b1, BMark.b0, BMark.b1],
          finiteHistLocalityPacketEncodeBHist H0,
          finiteHistLocalityPacketEncodeBHist H1,
          finiteHistLocalityPacketEncodeBHist L,
          finiteHistLocalityPacketEncodeBHist I,
          finiteHistLocalityPacketEncodeBHist S,
          finiteHistLocalityPacketEncodeBHist T,
          finiteHistLocalityPacketEncodeBHist C,
          finiteHistLocalityPacketEncodeBHist Q,
          finiteHistLocalityPacketEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro H0 H1 L I S T C Q N
  rfl

end BEDC.Derived.FiniteHistLocalityPacketUp
