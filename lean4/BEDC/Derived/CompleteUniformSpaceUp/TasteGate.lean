import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteUniformSpaceUp : Type where
  | mk (U F B L S R E H C P N : BHist) : CompleteUniformSpaceUp
  deriving DecidableEq

def completeUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeUniformSpaceEncodeBHist h

def completeUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeUniformSpaceDecodeBHist tail)

private theorem completeUniformSpaceDecode_encode_bhist :
    ∀ h : BHist, completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeUniformSpaceFields : CompleteUniformSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteUniformSpaceUp.mk U F B L S R E H C P N => [U, F, B, L, S, R, E, H, C, P, N]

def completeUniformSpaceToEventFlow : CompleteUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completeUniformSpaceFields x).map completeUniformSpaceEncodeBHist

def completeUniformSpaceFromEventFlow : EventFlow → Option CompleteUniformSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restF =>
      match restF with
      | [] => none
      | F :: restB =>
          match restB with
          | [] => none
          | B :: restL =>
              match restL with
              | [] => none
              | L :: restS =>
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
                                                    (CompleteUniformSpaceUp.mk
                                                      (completeUniformSpaceDecodeBHist U)
                                                      (completeUniformSpaceDecodeBHist F)
                                                      (completeUniformSpaceDecodeBHist B)
                                                      (completeUniformSpaceDecodeBHist L)
                                                      (completeUniformSpaceDecodeBHist S)
                                                      (completeUniformSpaceDecodeBHist R)
                                                      (completeUniformSpaceDecodeBHist E)
                                                      (completeUniformSpaceDecodeBHist H)
                                                      (completeUniformSpaceDecodeBHist C)
                                                      (completeUniformSpaceDecodeBHist P)
                                                      (completeUniformSpaceDecodeBHist N))
                                              | _ :: _ => none

private theorem completeUniformSpace_round_trip :
    ∀ x : CompleteUniformSpaceUp,
      completeUniformSpaceFromEventFlow (completeUniformSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U F B L S R E H C P N =>
      change
        some
          (CompleteUniformSpaceUp.mk
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist U))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist F))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist B))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist L))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist S))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist R))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist E))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist H))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist C))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist P))
            (completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist N))) =
          some (CompleteUniformSpaceUp.mk U F B L S R E H C P N)
      rw [completeUniformSpaceDecode_encode_bhist U, completeUniformSpaceDecode_encode_bhist F,
        completeUniformSpaceDecode_encode_bhist B, completeUniformSpaceDecode_encode_bhist L,
        completeUniformSpaceDecode_encode_bhist S, completeUniformSpaceDecode_encode_bhist R,
        completeUniformSpaceDecode_encode_bhist E, completeUniformSpaceDecode_encode_bhist H,
        completeUniformSpaceDecode_encode_bhist C, completeUniformSpaceDecode_encode_bhist P,
        completeUniformSpaceDecode_encode_bhist N]

private theorem completeUniformSpaceToEventFlow_injective {x y : CompleteUniformSpaceUp} :
    completeUniformSpaceToEventFlow x = completeUniformSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeUniformSpaceFromEventFlow (completeUniformSpaceToEventFlow x) =
        completeUniformSpaceFromEventFlow (completeUniformSpaceToEventFlow y) :=
    congrArg completeUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeUniformSpace_round_trip x).symm
      (Eq.trans hread (completeUniformSpace_round_trip y)))

instance completeUniformSpaceBHistCarrier : BHistCarrier CompleteUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeUniformSpaceToEventFlow
  fromEventFlow := completeUniformSpaceFromEventFlow

instance completeUniformSpaceChapterTasteGate : ChapterTasteGate CompleteUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeUniformSpaceFromEventFlow (completeUniformSpaceToEventFlow x) = some x
    exact completeUniformSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeUniformSpaceToEventFlow_injective heq)

theorem CompleteUniformSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeUniformSpaceDecodeBHist (completeUniformSpaceEncodeBHist h) = h) ∧
      (∀ x : CompleteUniformSpaceUp,
        completeUniformSpaceFromEventFlow (completeUniformSpaceToEventFlow x) = some x) ∧
        (∀ x y : CompleteUniformSpaceUp,
          completeUniformSpaceToEventFlow x = completeUniformSpaceToEventFlow y → x = y) ∧
          completeUniformSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨completeUniformSpaceDecode_encode_bhist,
      completeUniformSpace_round_trip,
      (fun _ _ heq => completeUniformSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompleteUniformSpaceUp
