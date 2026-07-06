import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxSumsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxSumsUp : Type where
  | mk (I P L U SL SU G R E H C Q N : BHist) : DarbouxSumsUp
  deriving DecidableEq

def darbouxSumsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxSumsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxSumsEncodeBHist h

def darbouxSumsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxSumsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxSumsDecodeBHist tail)

theorem DarbouxSumsTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, darbouxSumsDecodeBHist (darbouxSumsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxSumsFields : DarbouxSumsUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxSumsUp.mk I P L U SL SU G R E H C Q N =>
      [I, P, L, U, SL, SU, G, R, E, H, C, Q, N]

def darbouxSumsToEventFlow : DarbouxSumsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxSumsFields x).map darbouxSumsEncodeBHist

private def darbouxSumsEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxSumsEventAt index rest

def darbouxSumsFromEventFlow : EventFlow -> Option DarbouxSumsUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxSumsUp.mk
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 0 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 1 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 2 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 3 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 4 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 5 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 6 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 7 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 8 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 9 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 10 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 11 ef))
      (darbouxSumsDecodeBHist (darbouxSumsEventAt 12 ef)))

theorem DarbouxSumsTasteGate_single_carrier_alignment_round_trip
    (x : DarbouxSumsUp) :
    darbouxSumsFromEventFlow (darbouxSumsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I P L U SL SU G R E H C Q N =>
      change
        some
          (DarbouxSumsUp.mk
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist I))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist P))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist L))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist U))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist SL))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist SU))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist G))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist R))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist E))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist H))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist C))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist Q))
            (darbouxSumsDecodeBHist (darbouxSumsEncodeBHist N))) =
          some (DarbouxSumsUp.mk I P L U SL SU G R E H C Q N)
      rw [DarbouxSumsTasteGate_single_carrier_alignment_decode_encode I,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode L,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode U,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode SL,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode SU,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode G,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode E,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode C,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode Q,
        DarbouxSumsTasteGate_single_carrier_alignment_decode_encode N]

theorem DarbouxSumsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxSumsUp} :
    darbouxSumsToEventFlow x = darbouxSumsToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxSumsFromEventFlow (darbouxSumsToEventFlow x) =
        darbouxSumsFromEventFlow (darbouxSumsToEventFlow y) :=
    congrArg darbouxSumsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxSumsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxSumsTasteGate_single_carrier_alignment_round_trip y)))

theorem DarbouxSumsTasteGate_single_carrier_alignment_field_faithful :
    forall x y : DarbouxSumsUp, darbouxSumsFields x = darbouxSumsFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 P1 L1 U1 SL1 SU1 G1 R1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk I2 P2 L2 U2 SL2 SU2 G2 R2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance darbouxSumsBHistCarrier : BHistCarrier DarbouxSumsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxSumsToEventFlow
  fromEventFlow := darbouxSumsFromEventFlow

instance darbouxSumsChapterTasteGate : ChapterTasteGate DarbouxSumsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := DarbouxSumsTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxSumsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance darbouxSumsFieldFaithful : FieldFaithful DarbouxSumsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := darbouxSumsFields
  field_faithful := DarbouxSumsTasteGate_single_carrier_alignment_field_faithful

instance darbouxSumsNontrivial : BEDC.Meta.TasteGate.Nontrivial DarbouxSumsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DarbouxSumsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DarbouxSumsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DarbouxSumsTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DarbouxSumsUp) /\
      Nonempty (FieldFaithful DarbouxSumsUp) /\
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DarbouxSumsUp) /\
          (forall h : BHist, darbouxSumsDecodeBHist (darbouxSumsEncodeBHist h) = h) /\
            darbouxSumsEncodeBHist BHist.Empty = ([] : List BMark) /\
              (forall x : DarbouxSumsUp,
                darbouxSumsFromEventFlow (darbouxSumsToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨darbouxSumsChapterTasteGate⟩
  · constructor
    · exact ⟨darbouxSumsFieldFaithful⟩
    · constructor
      · exact ⟨darbouxSumsNontrivial⟩
      · constructor
        · exact DarbouxSumsTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · rfl
          · exact DarbouxSumsTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.DarbouxSumsUp
