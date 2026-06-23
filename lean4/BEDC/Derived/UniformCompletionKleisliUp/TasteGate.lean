import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionKleisliUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionKleisliUp : Type where
  | mk (U A B M S R E H C P N : BHist) : UniformCompletionKleisliUp
  deriving DecidableEq

def uniformCompletionKleisliEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionKleisliEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionKleisliEncodeBHist h

def uniformCompletionKleisliDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionKleisliDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionKleisliDecodeBHist tail)

private theorem UniformCompletionKleisliTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionKleisliToEventFlow : UniformCompletionKleisliUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionKleisliUp.mk U A B M S R E H C P N =>
      [uniformCompletionKleisliEncodeBHist U,
        uniformCompletionKleisliEncodeBHist A,
        uniformCompletionKleisliEncodeBHist B,
        uniformCompletionKleisliEncodeBHist M,
        uniformCompletionKleisliEncodeBHist S,
        uniformCompletionKleisliEncodeBHist R,
        uniformCompletionKleisliEncodeBHist E,
        uniformCompletionKleisliEncodeBHist H,
        uniformCompletionKleisliEncodeBHist C,
        uniformCompletionKleisliEncodeBHist P,
        uniformCompletionKleisliEncodeBHist N]

def uniformCompletionKleisliFromEventFlow : EventFlow → Option UniformCompletionKleisliUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restA =>
      match restA with
      | [] => none
      | A :: restB =>
          match restB with
          | [] => none
          | B :: restM =>
              match restM with
              | [] => none
              | M :: restS =>
                  match restS with
                  | [] => none
                  | S :: restR =>
                      match restR with
                      | [] => none
                      | R :: restE =>
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
                                                    (UniformCompletionKleisliUp.mk
                                                      (uniformCompletionKleisliDecodeBHist U)
                                                      (uniformCompletionKleisliDecodeBHist A)
                                                      (uniformCompletionKleisliDecodeBHist B)
                                                      (uniformCompletionKleisliDecodeBHist M)
                                                      (uniformCompletionKleisliDecodeBHist S)
                                                      (uniformCompletionKleisliDecodeBHist R)
                                                      (uniformCompletionKleisliDecodeBHist E)
                                                      (uniformCompletionKleisliDecodeBHist H)
                                                      (uniformCompletionKleisliDecodeBHist C)
                                                      (uniformCompletionKleisliDecodeBHist P)
                                                      (uniformCompletionKleisliDecodeBHist N))
                                              | _ :: _ => none

private theorem UniformCompletionKleisliTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCompletionKleisliUp,
      uniformCompletionKleisliFromEventFlow (uniformCompletionKleisliToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U A B M S R E H C P N =>
      change
        some
          (UniformCompletionKleisliUp.mk
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist U))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist A))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist B))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist M))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist S))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist R))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist E))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist H))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist C))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist P))
            (uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist N))) =
          some (UniformCompletionKleisliUp.mk U A B M S R E H C P N)
      rw [UniformCompletionKleisliTasteGate_single_carrier_alignment_decode U,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode A,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode B,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode M,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode S,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode R,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode E,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode H,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode C,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode P,
        UniformCompletionKleisliTasteGate_single_carrier_alignment_decode N]

private theorem UniformCompletionKleisliTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCompletionKleisliUp} :
    uniformCompletionKleisliToEventFlow x = uniformCompletionKleisliToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionKleisliFromEventFlow (uniformCompletionKleisliToEventFlow x) =
        uniformCompletionKleisliFromEventFlow (uniformCompletionKleisliToEventFlow y) :=
    congrArg uniformCompletionKleisliFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCompletionKleisliTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCompletionKleisliTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCompletionKleisliBHistCarrier : BHistCarrier UniformCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionKleisliToEventFlow
  fromEventFlow := uniformCompletionKleisliFromEventFlow

instance uniformCompletionKleisliChapterTasteGate :
    ChapterTasteGate UniformCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionKleisliFromEventFlow (uniformCompletionKleisliToEventFlow x) = some x
    exact UniformCompletionKleisliTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCompletionKleisliTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformCompletionKleisliTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        uniformCompletionKleisliDecodeBHist (uniformCompletionKleisliEncodeBHist h) = h) ∧
      (∀ x : UniformCompletionKleisliUp,
        uniformCompletionKleisliFromEventFlow (uniformCompletionKleisliToEventFlow x) =
          some x) ∧
        (∀ x y : UniformCompletionKleisliUp,
          uniformCompletionKleisliToEventFlow x = uniformCompletionKleisliToEventFlow y →
            x = y) ∧
          uniformCompletionKleisliEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformCompletionKleisliTasteGate_single_carrier_alignment_decode,
      UniformCompletionKleisliTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCompletionKleisliTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformCompletionKleisliUp
