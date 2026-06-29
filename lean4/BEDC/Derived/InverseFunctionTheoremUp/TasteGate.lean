import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InverseFunctionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InverseFunctionTheoremUp : Type where
  | mk (F U D L K G W S Q R H C P N : BHist) : InverseFunctionTheoremUp

def inverseFunctionTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inverseFunctionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inverseFunctionTheoremEncodeBHist h

def inverseFunctionTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inverseFunctionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inverseFunctionTheoremDecodeBHist tail)

private theorem InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inverseFunctionTheoremFields : InverseFunctionTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InverseFunctionTheoremUp.mk F U D L K G W S Q R H C P N =>
      [F, U, D, L, K, G, W, S, Q, R, H, C, P, N]

def inverseFunctionTheoremToEventFlow : InverseFunctionTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (inverseFunctionTheoremFields x).map inverseFunctionTheoremEncodeBHist

def inverseFunctionTheoremFromEventFlow : EventFlow -> Option InverseFunctionTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | U :: restU =>
          match restU with
          | D :: restD =>
              match restD with
              | L :: restL =>
                  match restL with
                  | K :: restK =>
                      match restK with
                      | G :: restG =>
                          match restG with
                          | W :: restW =>
                              match restW with
                              | S :: restS =>
                                  match restS with
                                  | Q :: restQ =>
                                      match restQ with
                                      | R :: restR =>
                                          match restR with
                                          | H :: restH =>
                                              match restH with
                                              | C :: restC =>
                                                  match restC with
                                                  | P :: restP =>
                                                      match restP with
                                                      | N :: restN =>
                                                          match restN with
                                                          | [] =>
                                                              some
                                                                (InverseFunctionTheoremUp.mk
                                                                  (inverseFunctionTheoremDecodeBHist F)
                                                                  (inverseFunctionTheoremDecodeBHist U)
                                                                  (inverseFunctionTheoremDecodeBHist D)
                                                                  (inverseFunctionTheoremDecodeBHist L)
                                                                  (inverseFunctionTheoremDecodeBHist K)
                                                                  (inverseFunctionTheoremDecodeBHist G)
                                                                  (inverseFunctionTheoremDecodeBHist W)
                                                                  (inverseFunctionTheoremDecodeBHist S)
                                                                  (inverseFunctionTheoremDecodeBHist Q)
                                                                  (inverseFunctionTheoremDecodeBHist R)
                                                                  (inverseFunctionTheoremDecodeBHist H)
                                                                  (inverseFunctionTheoremDecodeBHist C)
                                                                  (inverseFunctionTheoremDecodeBHist P)
                                                                  (inverseFunctionTheoremDecodeBHist N))
                                                          | _ :: _ => none
                                                      | [] => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem InverseFunctionTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : InverseFunctionTheoremUp,
      inverseFunctionTheoremFromEventFlow (inverseFunctionTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U D L K G W S Q R H C P N =>
      change
        some
            (InverseFunctionTheoremUp.mk
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist F))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist U))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist D))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist L))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist K))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist G))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist W))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist S))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist Q))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist R))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist H))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist C))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist P))
              (inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist N))) =
          some (InverseFunctionTheoremUp.mk F U D L K G W S Q R H C P N)
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode F]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode U]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode D]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode L]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode K]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode G]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode W]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode S]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode Q]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode R]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode H]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode C]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode P]
      rw [InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem InverseFunctionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : InverseFunctionTheoremUp} :
    inverseFunctionTheoremToEventFlow x = inverseFunctionTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inverseFunctionTheoremFromEventFlow (inverseFunctionTheoremToEventFlow x) =
        inverseFunctionTheoremFromEventFlow (inverseFunctionTheoremToEventFlow y) :=
    congrArg inverseFunctionTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InverseFunctionTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (InverseFunctionTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance inverseFunctionTheoremBHistCarrier : BHistCarrier InverseFunctionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inverseFunctionTheoremToEventFlow
  fromEventFlow := inverseFunctionTheoremFromEventFlow

instance inverseFunctionTheoremChapterTasteGate :
    ChapterTasteGate InverseFunctionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inverseFunctionTheoremFromEventFlow (inverseFunctionTheoremToEventFlow x) = some x
    exact InverseFunctionTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InverseFunctionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem InverseFunctionTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist,
        inverseFunctionTheoremDecodeBHist (inverseFunctionTheoremEncodeBHist h) = h) ∧
      (forall x : InverseFunctionTheoremUp,
        inverseFunctionTheoremFromEventFlow (inverseFunctionTheoremToEventFlow x) = some x) ∧
      (forall x y : InverseFunctionTheoremUp,
        inverseFunctionTheoremToEventFlow x = inverseFunctionTheoremToEventFlow y -> x = y) ∧
      inverseFunctionTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact InverseFunctionTheoremTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact InverseFunctionTheoremTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact InverseFunctionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.InverseFunctionTheoremUp
