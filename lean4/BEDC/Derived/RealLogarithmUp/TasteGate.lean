import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLogarithmUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLogarithmUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (P I B E A O C R H K N : BHist) : RealLogarithmUp
  deriving DecidableEq

def realLogarithmEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLogarithmEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLogarithmEncodeBHist h

def realLogarithmDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLogarithmDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLogarithmDecodeBHist tail)

private theorem RealLogarithmTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, realLogarithmDecodeBHist (realLogarithmEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLogarithmFields : RealLogarithmUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLogarithmUp.mk P I B E A O C R H K N => [P, I, B, E, A, O, C, R, H, K, N]

def realLogarithmToEventFlow : RealLogarithmUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realLogarithmFields x).map realLogarithmEncodeBHist

def realLogarithmFromEventFlow : EventFlow -> Option RealLogarithmUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | p :: restI =>
      match restI with
      | [] => none
      | i :: restB =>
          match restB with
          | [] => none
          | b :: restE =>
              match restE with
              | [] => none
              | e :: restA =>
                  match restA with
                  | [] => none
                  | a :: restO =>
                      match restO with
                      | [] => none
                      | o :: restC =>
                          match restC with
                          | [] => none
                          | c :: restR =>
                              match restR with
                              | [] => none
                              | r :: restH =>
                                  match restH with
                                  | [] => none
                                  | h :: restK =>
                                      match restK with
                                      | [] => none
                                      | k :: restN =>
                                          match restN with
                                          | [] => none
                                          | n :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (RealLogarithmUp.mk
                                                      (realLogarithmDecodeBHist p)
                                                      (realLogarithmDecodeBHist i)
                                                      (realLogarithmDecodeBHist b)
                                                      (realLogarithmDecodeBHist e)
                                                      (realLogarithmDecodeBHist a)
                                                      (realLogarithmDecodeBHist o)
                                                      (realLogarithmDecodeBHist c)
                                                      (realLogarithmDecodeBHist r)
                                                      (realLogarithmDecodeBHist h)
                                                      (realLogarithmDecodeBHist k)
                                                      (realLogarithmDecodeBHist n))
                                              | _ :: _ => none

private theorem RealLogarithmTasteGate_single_carrier_alignment_round_trip
    (x : RealLogarithmUp) :
    realLogarithmFromEventFlow (realLogarithmToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P I B E A O C R H K N =>
      change
        some
          (RealLogarithmUp.mk
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist P))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist I))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist B))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist E))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist A))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist O))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist C))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist R))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist H))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist K))
            (realLogarithmDecodeBHist (realLogarithmEncodeBHist N))) =
          some (RealLogarithmUp.mk P I B E A O C R H K N)
      rw [RealLogarithmTasteGate_single_carrier_alignment_decode_encode P,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode I,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode B,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode E,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode A,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode O,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode C,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode R,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode H,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode K,
        RealLogarithmTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealLogarithmTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealLogarithmUp} :
    realLogarithmToEventFlow x = realLogarithmToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLogarithmFromEventFlow (realLogarithmToEventFlow x) =
        realLogarithmFromEventFlow (realLogarithmToEventFlow y) :=
    congrArg realLogarithmFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealLogarithmTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealLogarithmTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealLogarithmTasteGate_single_carrier_alignment_fields_faithful
    (x y : RealLogarithmUp) :
    realLogarithmFields x = realLogarithmFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk P1 I1 B1 E1 A1 O1 C1 R1 H1 K1 N1 =>
      cases y with
      | mk P2 I2 B2 E2 A2 O2 C2 R2 H2 K2 N2 =>
          cases h
          rfl

instance realLogarithmBHistCarrier : BHistCarrier RealLogarithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLogarithmToEventFlow
  fromEventFlow := realLogarithmFromEventFlow

instance realLogarithmChapterTasteGate : ChapterTasteGate RealLogarithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLogarithmFromEventFlow (realLogarithmToEventFlow x) = some x
    exact RealLogarithmTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealLogarithmTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realLogarithmFieldFaithful : FieldFaithful RealLogarithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realLogarithmFields
  field_faithful := RealLogarithmTasteGate_single_carrier_alignment_fields_faithful

instance realLogarithmNontrivial : Nontrivial RealLogarithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealLogarithmUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealLogarithmUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealLogarithmUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLogarithmChapterTasteGate

theorem RealLogarithmTasteGate_single_carrier_alignment :
    (forall h : BHist, realLogarithmDecodeBHist (realLogarithmEncodeBHist h) = h) /\
      (forall x : RealLogarithmUp,
        realLogarithmFromEventFlow (realLogarithmToEventFlow x) = some x) /\
        Nonempty (BHistCarrier RealLogarithmUp) /\
          Nonempty (ChapterTasteGate RealLogarithmUp) /\
            realLogarithmEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealLogarithmTasteGate_single_carrier_alignment_decode_encode,
      RealLogarithmTasteGate_single_carrier_alignment_round_trip,
      ⟨realLogarithmBHistCarrier⟩,
      ⟨realLogarithmChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealLogarithmUp
