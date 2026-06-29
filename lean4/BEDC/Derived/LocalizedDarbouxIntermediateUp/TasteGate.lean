import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalizedDarbouxIntermediateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalizedDarbouxIntermediateUp : Type where
  | mk (I D B T W R E H C P N : BHist) : LocalizedDarbouxIntermediateUp
  deriving DecidableEq

def localizedDarbouxIntermediateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localizedDarbouxIntermediateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localizedDarbouxIntermediateEncodeBHist h

def localizedDarbouxIntermediateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localizedDarbouxIntermediateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localizedDarbouxIntermediateDecodeBHist tail)

private theorem localizedDarbouxIntermediate_decode_encode_bhist :
    ∀ h : BHist,
      localizedDarbouxIntermediateDecodeBHist
        (localizedDarbouxIntermediateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def localizedDarbouxIntermediateFields :
    LocalizedDarbouxIntermediateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalizedDarbouxIntermediateUp.mk I D B T W R E H C P N =>
      [I, D, B, T, W, R, E, H, C, P, N]

def localizedDarbouxIntermediateToEventFlow :
    LocalizedDarbouxIntermediateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (localizedDarbouxIntermediateFields x).map localizedDarbouxIntermediateEncodeBHist

def localizedDarbouxIntermediateFromEventFlow :
    EventFlow → Option LocalizedDarbouxIntermediateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LocalizedDarbouxIntermediateUp.mk
                                                      (localizedDarbouxIntermediateDecodeBHist I)
                                                      (localizedDarbouxIntermediateDecodeBHist D)
                                                      (localizedDarbouxIntermediateDecodeBHist B)
                                                      (localizedDarbouxIntermediateDecodeBHist T)
                                                      (localizedDarbouxIntermediateDecodeBHist W)
                                                      (localizedDarbouxIntermediateDecodeBHist R)
                                                      (localizedDarbouxIntermediateDecodeBHist E)
                                                      (localizedDarbouxIntermediateDecodeBHist H)
                                                      (localizedDarbouxIntermediateDecodeBHist C)
                                                      (localizedDarbouxIntermediateDecodeBHist P)
                                                      (localizedDarbouxIntermediateDecodeBHist N))
                                              | _ :: _ => none

private theorem localizedDarbouxIntermediate_round_trip :
    ∀ x : LocalizedDarbouxIntermediateUp,
      localizedDarbouxIntermediateFromEventFlow
        (localizedDarbouxIntermediateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D B T W R E H C P N =>
      change
        some
          (LocalizedDarbouxIntermediateUp.mk
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist I))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist D))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist B))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist T))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist W))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist R))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist E))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist H))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist C))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist P))
            (localizedDarbouxIntermediateDecodeBHist
              (localizedDarbouxIntermediateEncodeBHist N))) =
          some (LocalizedDarbouxIntermediateUp.mk I D B T W R E H C P N)
      rw [localizedDarbouxIntermediate_decode_encode_bhist I,
        localizedDarbouxIntermediate_decode_encode_bhist D,
        localizedDarbouxIntermediate_decode_encode_bhist B,
        localizedDarbouxIntermediate_decode_encode_bhist T,
        localizedDarbouxIntermediate_decode_encode_bhist W,
        localizedDarbouxIntermediate_decode_encode_bhist R,
        localizedDarbouxIntermediate_decode_encode_bhist E,
        localizedDarbouxIntermediate_decode_encode_bhist H,
        localizedDarbouxIntermediate_decode_encode_bhist C,
        localizedDarbouxIntermediate_decode_encode_bhist P,
        localizedDarbouxIntermediate_decode_encode_bhist N]

private theorem localizedDarbouxIntermediateToEventFlow_injective
    {x y : LocalizedDarbouxIntermediateUp} :
    localizedDarbouxIntermediateToEventFlow x =
      localizedDarbouxIntermediateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localizedDarbouxIntermediateFromEventFlow
          (localizedDarbouxIntermediateToEventFlow x) =
        localizedDarbouxIntermediateFromEventFlow
          (localizedDarbouxIntermediateToEventFlow y) :=
    congrArg localizedDarbouxIntermediateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localizedDarbouxIntermediate_round_trip x).symm
      (Eq.trans hread (localizedDarbouxIntermediate_round_trip y)))

instance localizedDarbouxIntermediateBHistCarrier :
    BHistCarrier LocalizedDarbouxIntermediateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localizedDarbouxIntermediateToEventFlow
  fromEventFlow := localizedDarbouxIntermediateFromEventFlow

instance localizedDarbouxIntermediateChapterTasteGate :
    ChapterTasteGate LocalizedDarbouxIntermediateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      localizedDarbouxIntermediateFromEventFlow
        (localizedDarbouxIntermediateToEventFlow x) = some x
    exact localizedDarbouxIntermediate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localizedDarbouxIntermediateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocalizedDarbouxIntermediateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localizedDarbouxIntermediateChapterTasteGate

theorem LocalizedDarbouxIntermediateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      localizedDarbouxIntermediateDecodeBHist
        (localizedDarbouxIntermediateEncodeBHist h) = h) ∧
      (∀ x : LocalizedDarbouxIntermediateUp,
        localizedDarbouxIntermediateFromEventFlow
          (localizedDarbouxIntermediateToEventFlow x) = some x) ∧
        (∀ x y : LocalizedDarbouxIntermediateUp,
          localizedDarbouxIntermediateToEventFlow x =
            localizedDarbouxIntermediateToEventFlow y → x = y) ∧
          localizedDarbouxIntermediateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact localizedDarbouxIntermediate_decode_encode_bhist
  · constructor
    · exact localizedDarbouxIntermediate_round_trip
    · constructor
      · intro x y heq
        exact localizedDarbouxIntermediateToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocalizedDarbouxIntermediateUp
