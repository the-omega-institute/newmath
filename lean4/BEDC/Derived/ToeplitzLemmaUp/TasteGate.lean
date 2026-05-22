import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ToeplitzLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ToeplitzLemmaUp : Type where
  | mk (A W R D T E H C P N : BHist) : ToeplitzLemmaUp
  deriving DecidableEq

def toeplitzLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: toeplitzLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: toeplitzLemmaEncodeBHist h

def toeplitzLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (toeplitzLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (toeplitzLemmaDecodeBHist tail)

private theorem toeplitzLemma_decode_encode_bhist :
    ∀ h : BHist, toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def toeplitzLemmaFields : ToeplitzLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ToeplitzLemmaUp.mk A W R D T E H C P N => [A, W, R, D, T, E, H, C, P, N]

def toeplitzLemmaToEventFlow : ToeplitzLemmaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (toeplitzLemmaFields x).map toeplitzLemmaEncodeBHist

def toeplitzLemmaFromEventFlow : EventFlow → Option ToeplitzLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: restA =>
      match restA with
      | W :: restW =>
          match restW with
          | R :: restR =>
              match restR with
              | D :: restD =>
                  match restD with
                  | T :: restT =>
                      match restT with
                      | E :: restE =>
                          match restE with
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
                                                (ToeplitzLemmaUp.mk
                                                  (toeplitzLemmaDecodeBHist A)
                                                  (toeplitzLemmaDecodeBHist W)
                                                  (toeplitzLemmaDecodeBHist R)
                                                  (toeplitzLemmaDecodeBHist D)
                                                  (toeplitzLemmaDecodeBHist T)
                                                  (toeplitzLemmaDecodeBHist E)
                                                  (toeplitzLemmaDecodeBHist H)
                                                  (toeplitzLemmaDecodeBHist C)
                                                  (toeplitzLemmaDecodeBHist P)
                                                  (toeplitzLemmaDecodeBHist N))
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

private theorem toeplitzLemma_round_trip :
    ∀ x : ToeplitzLemmaUp,
      toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A W R D T E H C P N =>
      change
        some
          (ToeplitzLemmaUp.mk
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist A))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist W))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist R))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist D))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist T))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist E))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist H))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist C))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist P))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist N))) =
          some (ToeplitzLemmaUp.mk A W R D T E H C P N)
      rw [toeplitzLemma_decode_encode_bhist A,
        toeplitzLemma_decode_encode_bhist W,
        toeplitzLemma_decode_encode_bhist R,
        toeplitzLemma_decode_encode_bhist D,
        toeplitzLemma_decode_encode_bhist T,
        toeplitzLemma_decode_encode_bhist E,
        toeplitzLemma_decode_encode_bhist H,
        toeplitzLemma_decode_encode_bhist C,
        toeplitzLemma_decode_encode_bhist P,
        toeplitzLemma_decode_encode_bhist N]

private theorem toeplitzLemmaToEventFlow_injective {x y : ToeplitzLemmaUp} :
    toeplitzLemmaToEventFlow x = toeplitzLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) :=
        (toeplitzLemma_round_trip x).symm
      _ = toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow y) :=
        congrArg toeplitzLemmaFromEventFlow hxy
      _ = some y := toeplitzLemma_round_trip y
  exact Option.some.inj optionEq

instance toeplitzLemmaBHistCarrier : BHistCarrier ToeplitzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toeplitzLemmaToEventFlow
  fromEventFlow := toeplitzLemmaFromEventFlow

instance toeplitzLemmaChapterTasteGate : ChapterTasteGate ToeplitzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x
    exact toeplitzLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toeplitzLemmaToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ToeplitzLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  toeplitzLemmaChapterTasteGate

theorem ToeplitzLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist h) = h) ∧
      (∀ x : ToeplitzLemmaUp,
        toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x) ∧
        (∀ x y : ToeplitzLemmaUp,
          toeplitzLemmaToEventFlow x = toeplitzLemmaToEventFlow y → x = y) ∧
          toeplitzLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨toeplitzLemma_decode_encode_bhist,
      toeplitzLemma_round_trip,
      (by
        intro x y heq
        exact toeplitzLemmaToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ToeplitzLemmaUp
