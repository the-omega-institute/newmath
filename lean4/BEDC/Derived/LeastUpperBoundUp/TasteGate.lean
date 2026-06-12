import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LeastUpperBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LeastUpperBoundUp : Type where
  | mk (S U A L D E H C P N : BHist) : LeastUpperBoundUp
  deriving DecidableEq

def leastUpperBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: leastUpperBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: leastUpperBoundEncodeBHist h

def leastUpperBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (leastUpperBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (leastUpperBoundDecodeBHist tail)

private theorem LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def leastUpperBoundFields : LeastUpperBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LeastUpperBoundUp.mk S U A L D E H C P N => [S, U, A, L, D, E, H, C, P, N]

def leastUpperBoundToEventFlow : LeastUpperBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (leastUpperBoundFields x).map leastUpperBoundEncodeBHist

def leastUpperBoundFromEventFlow : EventFlow → Option LeastUpperBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restU =>
      match restU with
      | [] => none
      | U :: restA =>
          match restA with
          | [] => none
          | A :: restL =>
              match restL with
              | [] => none
              | L :: restD =>
                  match restD with
                  | [] => none
                  | D :: restE =>
                      match restE with
                      | [] => none
                      | E :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (LeastUpperBoundUp.mk
                                                  (leastUpperBoundDecodeBHist S)
                                                  (leastUpperBoundDecodeBHist U)
                                                  (leastUpperBoundDecodeBHist A)
                                                  (leastUpperBoundDecodeBHist L)
                                                  (leastUpperBoundDecodeBHist D)
                                                  (leastUpperBoundDecodeBHist E)
                                                  (leastUpperBoundDecodeBHist H)
                                                  (leastUpperBoundDecodeBHist C)
                                                  (leastUpperBoundDecodeBHist P)
                                                  (leastUpperBoundDecodeBHist N))
                                          | _ :: _ => none

private theorem LeastUpperBoundTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LeastUpperBoundUp,
      leastUpperBoundFromEventFlow (leastUpperBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U A L D E H C P N =>
      change
        some
          (LeastUpperBoundUp.mk
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist S))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist U))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist A))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist L))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist D))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist E))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist H))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist C))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist P))
            (leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist N))) =
          some (LeastUpperBoundUp.mk S U A L D E H C P N)
      rw [LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode S,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode U,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode A,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode L,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode D,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode E,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode H,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode C,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode P,
        LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode N]

private theorem LeastUpperBoundTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LeastUpperBoundUp} :
    leastUpperBoundToEventFlow x = leastUpperBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      leastUpperBoundFromEventFlow (leastUpperBoundToEventFlow x) =
        leastUpperBoundFromEventFlow (leastUpperBoundToEventFlow y) :=
    congrArg leastUpperBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LeastUpperBoundTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LeastUpperBoundTasteGate_single_carrier_alignment_round_trip y)))

instance leastUpperBoundBHistCarrier : BHistCarrier LeastUpperBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := leastUpperBoundToEventFlow
  fromEventFlow := leastUpperBoundFromEventFlow

instance leastUpperBoundChapterTasteGate : ChapterTasteGate LeastUpperBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change leastUpperBoundFromEventFlow (leastUpperBoundToEventFlow x) = some x
    exact LeastUpperBoundTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LeastUpperBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LeastUpperBoundTasteGate_single_carrier_alignment :
    (∀ h : BHist, leastUpperBoundDecodeBHist (leastUpperBoundEncodeBHist h) = h) ∧
      (∀ x : LeastUpperBoundUp,
        leastUpperBoundFromEventFlow (leastUpperBoundToEventFlow x) = some x) ∧
      (∀ x y : LeastUpperBoundUp,
        leastUpperBoundToEventFlow x = leastUpperBoundToEventFlow y → x = y) ∧
      leastUpperBoundEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LeastUpperBoundTasteGate_single_carrier_alignment_decode_encode,
      LeastUpperBoundTasteGate_single_carrier_alignment_round_trip,
      fun x y heq => LeastUpperBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LeastUpperBoundUp
