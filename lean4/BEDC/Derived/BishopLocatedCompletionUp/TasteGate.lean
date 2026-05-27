import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionUp : Type where
  | mk (L S M R E H C P N : BHist) : BishopLocatedCompletionUp
  deriving DecidableEq

def bishopLocatedCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionEncodeBHist h

def bishopLocatedCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionDecodeBHist tail)

private theorem bishopLocatedCompletion_decode_encode :
    ∀ h : BHist,
      bishopLocatedCompletionDecodeBHist (bishopLocatedCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionFields : BishopLocatedCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionUp.mk L S M R E H C P N =>
      [L, S, M, R, E, H, C, P, N]

def bishopLocatedCompletionToEventFlow : BishopLocatedCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bishopLocatedCompletionEncodeBHist (bishopLocatedCompletionFields x)

def bishopLocatedCompletionFromEventFlow :
    EventFlow → Option BishopLocatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | L :: restL =>
        match restL with
        | [] => none
        | S :: restS =>
            match restS with
            | [] => none
            | M :: restM =>
                match restM with
                | [] => none
                | R :: restR =>
                    match restR with
                    | [] => none
                    | E :: restE =>
                        match restE with
                        | [] => none
                        | H :: restH =>
                            match restH with
                            | [] => none
                            | C :: restC =>
                                match restC with
                                | [] => none
                                | P :: restP =>
                                    match restP with
                                    | [] => none
                                    | N :: restN =>
                                        match restN with
                                        | [] =>
                                            some
                                              (BishopLocatedCompletionUp.mk
                                                (bishopLocatedCompletionDecodeBHist L)
                                                (bishopLocatedCompletionDecodeBHist S)
                                                (bishopLocatedCompletionDecodeBHist M)
                                                (bishopLocatedCompletionDecodeBHist R)
                                                (bishopLocatedCompletionDecodeBHist E)
                                                (bishopLocatedCompletionDecodeBHist H)
                                                (bishopLocatedCompletionDecodeBHist C)
                                                (bishopLocatedCompletionDecodeBHist P)
                                                (bishopLocatedCompletionDecodeBHist N))
                                        | _ :: _ => none

private theorem bishopLocatedCompletion_round_trip :
    ∀ x : BishopLocatedCompletionUp,
      bishopLocatedCompletionFromEventFlow
          (bishopLocatedCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L S M R E H C P N =>
      exact
        congrArg (fun z => some z)
          (congr
            (congr
              (congr
                (congr
                  (congr
                    (congr
                      (congr
                        (congr
                          (congrArg BishopLocatedCompletionUp.mk
                            (bishopLocatedCompletion_decode_encode L))
                          (bishopLocatedCompletion_decode_encode S))
                        (bishopLocatedCompletion_decode_encode M))
                      (bishopLocatedCompletion_decode_encode R))
                    (bishopLocatedCompletion_decode_encode E))
                  (bishopLocatedCompletion_decode_encode H))
                (bishopLocatedCompletion_decode_encode C))
              (bishopLocatedCompletion_decode_encode P))
            (bishopLocatedCompletion_decode_encode N))

private theorem bishopLocatedCompletionToEventFlow_injective
    {x y : BishopLocatedCompletionUp} :
    bishopLocatedCompletionToEventFlow x =
        bishopLocatedCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionFromEventFlow (bishopLocatedCompletionToEventFlow x) =
        bishopLocatedCompletionFromEventFlow (bishopLocatedCompletionToEventFlow y) :=
    congrArg bishopLocatedCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bishopLocatedCompletion_round_trip x).symm
      (Eq.trans hread (bishopLocatedCompletion_round_trip y)))

instance bishopLocatedCompletionBHistCarrier :
    BHistCarrier BishopLocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionToEventFlow
  fromEventFlow := bishopLocatedCompletionFromEventFlow

instance bishopLocatedCompletionChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    cases x with
    | mk L S M R E H C P N =>
        exact bishopLocatedCompletion_round_trip
          (BishopLocatedCompletionUp.mk L S M R E H C P N)
  layer_separation := by
    intro x y hxy heq
    apply hxy
    apply bishopLocatedCompletionToEventFlow_injective
    simpa only [BHistCarrier.toEventFlow] using heq

def taste_gate : ChapterTasteGate BishopLocatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletionChapterTasteGate

theorem BishopLocatedCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedCompletionDecodeBHist
      (bishopLocatedCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopLocatedCompletionUp) ∧
        Nonempty (ChapterTasteGate BishopLocatedCompletionUp) ∧
          bishopLocatedCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bishopLocatedCompletion_decode_encode,
      ⟨bishopLocatedCompletionBHistCarrier⟩,
      ⟨bishopLocatedCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopLocatedCompletionUp
