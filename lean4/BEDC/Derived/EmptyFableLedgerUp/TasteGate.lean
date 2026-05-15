import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyFableLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyFableLedgerUp : Type where
  | mk : (history trace selectors fable cont provenance name : BHist) → EmptyFableLedgerUp
  deriving DecidableEq

def emptyFableLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyFableLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyFableLedgerEncodeBHist h

def emptyFableLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyFableLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyFableLedgerDecodeBHist tail)

private theorem emptyFableLedgerDecode_encode_bhist :
    ∀ h : BHist, emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def emptyFableLedgerToEventFlow : EmptyFableLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyFableLedgerUp.mk history trace selectors fable cont provenance name =>
      [[BMark.b0],
        emptyFableLedgerEncodeBHist history,
        [BMark.b1, BMark.b0],
        emptyFableLedgerEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        emptyFableLedgerEncodeBHist selectors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableLedgerEncodeBHist fable,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableLedgerEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        emptyFableLedgerEncodeBHist name]

def emptyFableLedgerFromEventFlow : EventFlow → Option EmptyFableLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectors :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fable :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | cont :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (EmptyFableLedgerUp.mk
                                                                  (emptyFableLedgerDecodeBHist
                                                                    history)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    trace)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    selectors)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    fable)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    cont)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    provenance)
                                                                  (emptyFableLedgerDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem emptyFableLedger_round_trip :
    ∀ x : EmptyFableLedgerUp,
      emptyFableLedgerFromEventFlow (emptyFableLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history trace selectors fable cont provenance name =>
      change
        some
          (EmptyFableLedgerUp.mk
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist history))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist trace))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist selectors))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist fable))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist cont))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist provenance))
            (emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist name))) =
          some
            (EmptyFableLedgerUp.mk history trace selectors fable cont provenance name)
      rw [emptyFableLedgerDecode_encode_bhist history,
        emptyFableLedgerDecode_encode_bhist trace,
        emptyFableLedgerDecode_encode_bhist selectors,
        emptyFableLedgerDecode_encode_bhist fable,
        emptyFableLedgerDecode_encode_bhist cont,
        emptyFableLedgerDecode_encode_bhist provenance,
        emptyFableLedgerDecode_encode_bhist name]

private theorem emptyFableLedgerToEventFlow_injective {x y : EmptyFableLedgerUp} :
    emptyFableLedgerToEventFlow x = emptyFableLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      emptyFableLedgerFromEventFlow (emptyFableLedgerToEventFlow x) =
        emptyFableLedgerFromEventFlow (emptyFableLedgerToEventFlow y) :=
    congrArg emptyFableLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (emptyFableLedger_round_trip x).symm
      (Eq.trans hread (emptyFableLedger_round_trip y)))

def emptyFableLedgerFields : EmptyFableLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyFableLedgerUp.mk history trace selectors fable cont provenance name =>
      [history, trace, selectors, fable, cont, provenance, name]

private theorem emptyFableLedger_field_faithful :
    ∀ x y : EmptyFableLedgerUp,
      emptyFableLedgerFields x = emptyFableLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk history trace selectors fable cont provenance name =>
      cases y with
      | mk history' trace' selectors' fable' cont' provenance' name' =>
          cases hfields
          rfl

instance emptyFableLedgerBHistCarrier : BHistCarrier EmptyFableLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyFableLedgerToEventFlow
  fromEventFlow := emptyFableLedgerFromEventFlow

instance emptyFableLedgerChapterTasteGate : ChapterTasteGate EmptyFableLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := emptyFableLedger_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (emptyFableLedgerToEventFlow_injective heq)

instance emptyFableLedgerFieldFaithful : FieldFaithful EmptyFableLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := emptyFableLedgerFields
  field_faithful := emptyFableLedger_field_faithful

instance emptyFableLedgerNontrivial : Nontrivial EmptyFableLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmptyFableLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EmptyFableLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def emptyFableLedgerTasteGate : ChapterTasteGate EmptyFableLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyFableLedgerChapterTasteGate

theorem EmptyFableLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        emptyFableLedgerDecodeBHist (emptyFableLedgerEncodeBHist h) = h) ∧
      (∀ x : EmptyFableLedgerUp,
        emptyFableLedgerFromEventFlow (emptyFableLedgerToEventFlow x) = some x) ∧
        (∀ x y : EmptyFableLedgerUp,
          emptyFableLedgerToEventFlow x = emptyFableLedgerToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate EmptyFableLedgerUp) ∧
            Nonempty (FieldFaithful EmptyFableLedgerUp) ∧
              Nonempty (Nontrivial EmptyFableLedgerUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact emptyFableLedgerDecode_encode_bhist
  · constructor
    · exact emptyFableLedger_round_trip
    · constructor
      · intro x y heq
        exact emptyFableLedgerToEventFlow_injective heq
      · exact
          And.intro ⟨emptyFableLedgerChapterTasteGate⟩
            (And.intro ⟨emptyFableLedgerFieldFaithful⟩
              ⟨emptyFableLedgerNontrivial⟩)

end BEDC.Derived.EmptyFableLedgerUp.TasteGate
