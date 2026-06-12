import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedCompactIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedCompactIntersectionUp : Type where
  | mk (C J W F S R E H P N : BHist) : NestedCompactIntersectionUp
  deriving DecidableEq

def nestedCompactIntersectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedCompactIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedCompactIntersectionEncodeBHist h

def nestedCompactIntersectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedCompactIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedCompactIntersectionDecodeBHist tail)

private theorem nestedCompactIntersectionDecode_encode_bhist :
    ∀ h : BHist,
      nestedCompactIntersectionDecodeBHist
        (nestedCompactIntersectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedCompactIntersectionFields : NestedCompactIntersectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedCompactIntersectionUp.mk C J W F S R E H P N => [C, J, W, F, S, R, E, H, P, N]

def nestedCompactIntersectionToEventFlow :
    NestedCompactIntersectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedCompactIntersectionFields x).map nestedCompactIntersectionEncodeBHist

def nestedCompactIntersectionFromEventFlow :
    EventFlow → Option NestedCompactIntersectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: restJ =>
      match restJ with
      | [] => none
      | J :: restW =>
          match restW with
          | [] => none
          | W :: restF =>
              match restF with
              | [] => none
              | F :: restS =>
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
                              | H :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (NestedCompactIntersectionUp.mk
                                                  (nestedCompactIntersectionDecodeBHist C)
                                                  (nestedCompactIntersectionDecodeBHist J)
                                                  (nestedCompactIntersectionDecodeBHist W)
                                                  (nestedCompactIntersectionDecodeBHist F)
                                                  (nestedCompactIntersectionDecodeBHist S)
                                                  (nestedCompactIntersectionDecodeBHist R)
                                                  (nestedCompactIntersectionDecodeBHist E)
                                                  (nestedCompactIntersectionDecodeBHist H)
                                                  (nestedCompactIntersectionDecodeBHist P)
                                                  (nestedCompactIntersectionDecodeBHist N))
                                          | _ :: _ => none

private theorem nestedCompactIntersection_round_trip :
    ∀ x : NestedCompactIntersectionUp,
      nestedCompactIntersectionFromEventFlow
        (nestedCompactIntersectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C J W F S R E H P N =>
      change
        some
          (NestedCompactIntersectionUp.mk
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist C))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist J))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist W))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist F))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist S))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist R))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist E))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist H))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist P))
            (nestedCompactIntersectionDecodeBHist (nestedCompactIntersectionEncodeBHist N))) =
          some (NestedCompactIntersectionUp.mk C J W F S R E H P N)
      rw [nestedCompactIntersectionDecode_encode_bhist C,
        nestedCompactIntersectionDecode_encode_bhist J,
        nestedCompactIntersectionDecode_encode_bhist W,
        nestedCompactIntersectionDecode_encode_bhist F,
        nestedCompactIntersectionDecode_encode_bhist S,
        nestedCompactIntersectionDecode_encode_bhist R,
        nestedCompactIntersectionDecode_encode_bhist E,
        nestedCompactIntersectionDecode_encode_bhist H,
        nestedCompactIntersectionDecode_encode_bhist P,
        nestedCompactIntersectionDecode_encode_bhist N]

private theorem nestedCompactIntersectionToEventFlow_injective
    {x y : NestedCompactIntersectionUp} :
    nestedCompactIntersectionToEventFlow x =
      nestedCompactIntersectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow x) =
        nestedCompactIntersectionFromEventFlow (nestedCompactIntersectionToEventFlow y) :=
    congrArg nestedCompactIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedCompactIntersection_round_trip x).symm
      (Eq.trans hread (nestedCompactIntersection_round_trip y)))

instance nestedCompactIntersectionBHistCarrier :
    BHistCarrier NestedCompactIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedCompactIntersectionToEventFlow
  fromEventFlow := nestedCompactIntersectionFromEventFlow

instance nestedCompactIntersectionChapterTasteGate :
    ChapterTasteGate NestedCompactIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedCompactIntersectionFromEventFlow
        (nestedCompactIntersectionToEventFlow x) = some x
    exact nestedCompactIntersection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedCompactIntersectionToEventFlow_injective heq)

theorem NestedCompactIntersectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedCompactIntersectionDecodeBHist
      (nestedCompactIntersectionEncodeBHist h) = h) ∧
      (∀ x : NestedCompactIntersectionUp,
        nestedCompactIntersectionFromEventFlow
          (nestedCompactIntersectionToEventFlow x) = some x) ∧
        (∀ x y : NestedCompactIntersectionUp,
          nestedCompactIntersectionToEventFlow x =
            nestedCompactIntersectionToEventFlow y -> x = y) ∧
          nestedCompactIntersectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨nestedCompactIntersectionDecode_encode_bhist,
      nestedCompactIntersection_round_trip,
      (fun _ _ heq => nestedCompactIntersectionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.NestedCompactIntersectionUp
