import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCompletionUp : Type where
  | mk (L U G W S R A E H C P N : BHist) : DedekindCutCompletionUp
  deriving DecidableEq

def dedekindCutCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCompletionEncodeBHist h

def dedekindCutCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCompletionDecodeBHist tail)

private theorem dedekindCutCompletion_decode_encode :
    forall h : BHist,
      dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dedekindCutCompletionFields : DedekindCutCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCompletionUp.mk L U G W S R A E H C P N => [L, U, G, W, S, R, A, E, H, C, P, N]

def dedekindCutCompletionToEventFlow : DedekindCutCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindCutCompletionFields x).map dedekindCutCompletionEncodeBHist

def dedekindCutCompletionFromEventFlow : EventFlow -> Option DedekindCutCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restU =>
      match restU with
      | [] => none
      | U :: restG =>
          match restG with
          | [] => none
          | G :: restW =>
              match restW with
              | [] => none
              | W :: restS =>
                  match restS with
                  | [] => none
                  | S :: restR =>
                      match restR with
                      | [] => none
                      | R :: restA =>
                          match restA with
                          | [] => none
                          | A :: restE =>
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
                                                        (DedekindCutCompletionUp.mk
                                                          (dedekindCutCompletionDecodeBHist L)
                                                          (dedekindCutCompletionDecodeBHist U)
                                                          (dedekindCutCompletionDecodeBHist G)
                                                          (dedekindCutCompletionDecodeBHist W)
                                                          (dedekindCutCompletionDecodeBHist S)
                                                          (dedekindCutCompletionDecodeBHist R)
                                                          (dedekindCutCompletionDecodeBHist A)
                                                          (dedekindCutCompletionDecodeBHist E)
                                                          (dedekindCutCompletionDecodeBHist H)
                                                          (dedekindCutCompletionDecodeBHist C)
                                                          (dedekindCutCompletionDecodeBHist P)
                                                          (dedekindCutCompletionDecodeBHist N))
                                                  | _ :: _ => none

private theorem dedekindCutCompletion_round_trip :
    forall x : DedekindCutCompletionUp,
      dedekindCutCompletionFromEventFlow (dedekindCutCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U G W S R A E H C P N =>
      change
        some
          (DedekindCutCompletionUp.mk
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist L))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist U))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist G))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist W))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist S))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist R))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist A))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist E))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist H))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist C))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist P))
            (dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist N))) =
          some (DedekindCutCompletionUp.mk L U G W S R A E H C P N)
      rw [dedekindCutCompletion_decode_encode L, dedekindCutCompletion_decode_encode U,
        dedekindCutCompletion_decode_encode G, dedekindCutCompletion_decode_encode W,
        dedekindCutCompletion_decode_encode S, dedekindCutCompletion_decode_encode R,
        dedekindCutCompletion_decode_encode A, dedekindCutCompletion_decode_encode E,
        dedekindCutCompletion_decode_encode H, dedekindCutCompletion_decode_encode C,
        dedekindCutCompletion_decode_encode P, dedekindCutCompletion_decode_encode N]

private theorem dedekindCutCompletionToEventFlow_injective {x y : DedekindCutCompletionUp} :
    dedekindCutCompletionToEventFlow x = dedekindCutCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCompletionFromEventFlow (dedekindCutCompletionToEventFlow x) =
        dedekindCutCompletionFromEventFlow (dedekindCutCompletionToEventFlow y) :=
    congrArg dedekindCutCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindCutCompletion_round_trip x).symm
      (Eq.trans hread (dedekindCutCompletion_round_trip y)))

instance dedekindCutCompletionBHistCarrier : BHistCarrier DedekindCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCompletionToEventFlow
  fromEventFlow := dedekindCutCompletionFromEventFlow

instance dedekindCutCompletionChapterTasteGate : ChapterTasteGate DedekindCutCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dedekindCutCompletionFromEventFlow (dedekindCutCompletionToEventFlow x) = some x
    exact dedekindCutCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DedekindCutCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCompletionChapterTasteGate

theorem DedekindCutCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dedekindCutCompletionDecodeBHist (dedekindCutCompletionEncodeBHist h) = h) ∧
      (forall x : DedekindCutCompletionUp,
        dedekindCutCompletionFromEventFlow (dedekindCutCompletionToEventFlow x) = some x) ∧
        (forall x y : DedekindCutCompletionUp,
          dedekindCutCompletionToEventFlow x = dedekindCutCompletionToEventFlow y -> x = y) ∧
          dedekindCutCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dedekindCutCompletion_decode_encode
  constructor
  · exact dedekindCutCompletion_round_trip
  constructor
  · intro x y heq
    exact dedekindCutCompletionToEventFlow_injective heq
  · rfl

end BEDC.Derived.DedekindCutCompletionUp
