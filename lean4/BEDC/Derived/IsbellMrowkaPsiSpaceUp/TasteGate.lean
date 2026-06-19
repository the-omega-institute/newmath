import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsbellMrowkaPsiSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IsbellMrowkaPsiSpaceUp : Type where
  | mk (isolated family topology singleton tail observable membership window transport replay
      provenance localName : BHist) : IsbellMrowkaPsiSpaceUp
  deriving DecidableEq

def isbellMrowkaPsiSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isbellMrowkaPsiSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isbellMrowkaPsiSpaceEncodeBHist h

def isbellMrowkaPsiSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isbellMrowkaPsiSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isbellMrowkaPsiSpaceDecodeBHist tail)

private theorem IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def isbellMrowkaPsiSpaceFields : IsbellMrowkaPsiSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IsbellMrowkaPsiSpaceUp.mk isolated family topology singleton tail observable membership
      window transport replay provenance localName =>
      [isolated, family, topology, singleton, tail, observable, membership, window,
        transport, replay, provenance, localName]

def isbellMrowkaPsiSpaceToEventFlow : IsbellMrowkaPsiSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IsbellMrowkaPsiSpaceUp.mk isolated family topology singleton tail observable membership
      window transport replay provenance localName =>
      [[BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist isolated,
        [BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist family,
        [BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist topology,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist singleton,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist observable,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist membership,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        isbellMrowkaPsiSpaceEncodeBHist localName]

def isbellMrowkaPsiSpaceFromEventFlow : EventFlow → Option IsbellMrowkaPsiSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | isolated :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | family :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | topology :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | singleton :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tail :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | observable :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | membership :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | window :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | replay :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | localName :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (IsbellMrowkaPsiSpaceUp.mk
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist isolated)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist family)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist topology)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist singleton)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist tail)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist observable)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist membership)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist window)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist transport)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist replay)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist provenance)
                                                                                                          (isbellMrowkaPsiSpaceDecodeBHist localName))
                                                                                                  | _ :: _ => none

private theorem IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IsbellMrowkaPsiSpaceUp,
      isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk isolated family topology singleton tail observable membership window transport replay
      provenance localName =>
      change
        some
          (IsbellMrowkaPsiSpaceUp.mk
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist isolated))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist family))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist topology))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist singleton))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist tail))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist observable))
            (isbellMrowkaPsiSpaceDecodeBHist
              (isbellMrowkaPsiSpaceEncodeBHist membership))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist window))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist transport))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist replay))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist provenance))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist localName))) =
          some
            (IsbellMrowkaPsiSpaceUp.mk isolated family topology singleton tail observable
              membership window transport replay provenance localName)
      rw [IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode isolated,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode family,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode topology,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode singleton,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode tail,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode observable,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode membership,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode window,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode transport,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode replay,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode provenance,
        IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IsbellMrowkaPsiSpaceUp} :
    isbellMrowkaPsiSpaceToEventFlow x = isbellMrowkaPsiSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) =
        isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow y) :=
    congrArg isbellMrowkaPsiSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance isbellMrowkaPsiSpaceBHistCarrier : BHistCarrier IsbellMrowkaPsiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isbellMrowkaPsiSpaceToEventFlow
  fromEventFlow := isbellMrowkaPsiSpaceFromEventFlow

instance isbellMrowkaPsiSpaceChapterTasteGate :
    ChapterTasteGate IsbellMrowkaPsiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) = some x
    exact IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance isbellMrowkaPsiSpaceNontrivial : Nontrivial IsbellMrowkaPsiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IsbellMrowkaPsiSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      IsbellMrowkaPsiSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate IsbellMrowkaPsiSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isbellMrowkaPsiSpaceChapterTasteGate

theorem IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist h) = h) ∧
      (∀ x : IsbellMrowkaPsiSpaceUp,
        isbellMrowkaPsiSpaceFromEventFlow
          (isbellMrowkaPsiSpaceToEventFlow x) = some x) ∧
        (∀ x y : IsbellMrowkaPsiSpaceUp,
          isbellMrowkaPsiSpaceToEventFlow x =
            isbellMrowkaPsiSpaceToEventFlow y → x = y) ∧
          isbellMrowkaPsiSpaceEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : IsbellMrowkaPsiSpaceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · constructor
        · rfl
        · exact
            ⟨IsbellMrowkaPsiSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty,
              IsbellMrowkaPsiSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.IsbellMrowkaPsiSpaceUp
