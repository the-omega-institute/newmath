import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HellySelectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HellySelectionUp : Type where
  | mk (B A W S R E T C P N : BHist) : HellySelectionUp
  deriving DecidableEq

def hellySelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hellySelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hellySelectionEncodeBHist h

def hellySelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hellySelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hellySelectionDecodeBHist tail)

private theorem hellySelectionDecode_encode_bhist :
    ∀ h : BHist, hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hellySelectionFields : HellySelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HellySelectionUp.mk B A W S R E T C P N =>
      [B, A, W, S, R, E, T, C, P, N]

def hellySelectionToEventFlow : HellySelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hellySelectionFields x).map hellySelectionEncodeBHist

def hellySelectionFromEventFlow : EventFlow → Option HellySelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | b :: rest0 =>
      match rest0 with
      | [] => none
      | a :: rest1 =>
          match rest1 with
          | [] => none
          | w :: rest2 =>
              match rest2 with
              | [] => none
              | s :: rest3 =>
                  match rest3 with
                  | [] => none
                  | r :: rest4 =>
                      match rest4 with
                      | [] => none
                      | e :: rest5 =>
                          match rest5 with
                          | [] => none
                          | t :: rest6 =>
                              match rest6 with
                              | [] => none
                              | c :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | p :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | n :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some (HellySelectionUp.mk (hellySelectionDecodeBHist b) (hellySelectionDecodeBHist a) (hellySelectionDecodeBHist w) (hellySelectionDecodeBHist s) (hellySelectionDecodeBHist r) (hellySelectionDecodeBHist e) (hellySelectionDecodeBHist t) (hellySelectionDecodeBHist c) (hellySelectionDecodeBHist p) (hellySelectionDecodeBHist n))
                                          | _ :: _ => none
private theorem hellySelection_round_trip :
    ∀ x : HellySelectionUp,
      hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A W S R E T C P N =>
      change
        some (HellySelectionUp.mk (hellySelectionDecodeBHist (hellySelectionEncodeBHist B)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist A)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist W)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist S)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist R)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist E)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist T)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist C)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist P)) (hellySelectionDecodeBHist (hellySelectionEncodeBHist N))) =
          some (HellySelectionUp.mk B A W S R E T C P N)
      rw [hellySelectionDecode_encode_bhist B,
        hellySelectionDecode_encode_bhist A,
        hellySelectionDecode_encode_bhist W,
        hellySelectionDecode_encode_bhist S,
        hellySelectionDecode_encode_bhist R,
        hellySelectionDecode_encode_bhist E,
        hellySelectionDecode_encode_bhist T,
        hellySelectionDecode_encode_bhist C,
        hellySelectionDecode_encode_bhist P,
        hellySelectionDecode_encode_bhist N]

private theorem hellySelectionToEventFlow_injective
    {x y : HellySelectionUp} :
    hellySelectionToEventFlow x = hellySelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hellySelectionFromEventFlow (hellySelectionToEventFlow x) =
        hellySelectionFromEventFlow (hellySelectionToEventFlow y) :=
    congrArg hellySelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hellySelection_round_trip x).symm
      (Eq.trans hread (hellySelection_round_trip y)))

private theorem hellySelection_field_faithful :
    ∀ x y : HellySelectionUp,
      hellySelectionFields x = hellySelectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance hellySelectionBHistCarrier : BHistCarrier HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hellySelectionToEventFlow
  fromEventFlow := hellySelectionFromEventFlow

instance hellySelectionChapterTasteGate :
    ChapterTasteGate HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x
    exact hellySelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hellySelectionToEventFlow_injective heq)

instance hellySelectionFieldFaithful :
    FieldFaithful HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hellySelectionFields
  field_faithful := hellySelection_field_faithful

instance hellySelectionNontrivial : Nontrivial HellySelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HellySelectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HellySelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HellySelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hellySelectionChapterTasteGate

theorem HellySelectionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, hellySelectionDecodeBHist (hellySelectionEncodeBHist h) = h) ∧
      (∀ x : HellySelectionUp,
        hellySelectionFromEventFlow (hellySelectionToEventFlow x) = some x) ∧
        (∀ x y : HellySelectionUp,
          hellySelectionToEventFlow x = hellySelectionToEventFlow y → x = y) ∧
          hellySelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨hellySelectionDecode_encode_bhist,
      hellySelection_round_trip,
      (fun _ _ heq => hellySelectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HellySelectionUp.TasteGate
