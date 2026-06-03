import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedHeineBorelSubcoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedHeineBorelSubcoverUp : Type where
  | mk (I F L H R D E T C P N : BHist) : LocatedHeineBorelSubcoverUp
  deriving DecidableEq

def locatedHeineBorelSubcoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedHeineBorelSubcoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedHeineBorelSubcoverEncodeBHist h

def locatedHeineBorelSubcoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedHeineBorelSubcoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedHeineBorelSubcoverDecodeBHist tail)

private theorem LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedHeineBorelSubcoverDecodeBHist
        (locatedHeineBorelSubcoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedHeineBorelSubcoverToEventFlow :
    LocatedHeineBorelSubcoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedHeineBorelSubcoverUp.mk I F L H R D E T C P N =>
      [locatedHeineBorelSubcoverEncodeBHist I,
        locatedHeineBorelSubcoverEncodeBHist F,
        locatedHeineBorelSubcoverEncodeBHist L,
        locatedHeineBorelSubcoverEncodeBHist H,
        locatedHeineBorelSubcoverEncodeBHist R,
        locatedHeineBorelSubcoverEncodeBHist D,
        locatedHeineBorelSubcoverEncodeBHist E,
        locatedHeineBorelSubcoverEncodeBHist T,
        locatedHeineBorelSubcoverEncodeBHist C,
        locatedHeineBorelSubcoverEncodeBHist P,
        locatedHeineBorelSubcoverEncodeBHist N]

def locatedHeineBorelSubcoverFromEventFlow :
    EventFlow → Option LocatedHeineBorelSubcoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | H :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
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
                                                    (LocatedHeineBorelSubcoverUp.mk
                                                      (locatedHeineBorelSubcoverDecodeBHist I)
                                                      (locatedHeineBorelSubcoverDecodeBHist F)
                                                      (locatedHeineBorelSubcoverDecodeBHist L)
                                                      (locatedHeineBorelSubcoverDecodeBHist H)
                                                      (locatedHeineBorelSubcoverDecodeBHist R)
                                                      (locatedHeineBorelSubcoverDecodeBHist D)
                                                      (locatedHeineBorelSubcoverDecodeBHist E)
                                                      (locatedHeineBorelSubcoverDecodeBHist T)
                                                      (locatedHeineBorelSubcoverDecodeBHist C)
                                                      (locatedHeineBorelSubcoverDecodeBHist P)
                                                      (locatedHeineBorelSubcoverDecodeBHist N))
                                              | _ :: _ => none

private theorem LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedHeineBorelSubcoverUp,
      locatedHeineBorelSubcoverFromEventFlow
        (locatedHeineBorelSubcoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F L H R D E T C P N =>
      change
        some
          (LocatedHeineBorelSubcoverUp.mk
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist I))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist F))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist L))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist H))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist R))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist D))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist E))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist T))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist C))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist P))
            (locatedHeineBorelSubcoverDecodeBHist
              (locatedHeineBorelSubcoverEncodeBHist N))) =
          some (LocatedHeineBorelSubcoverUp.mk I F L H R D E T C P N)
      rw [LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode I,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode F,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode L,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode H,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode R,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode D,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode E,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode T,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode C,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode P,
        LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedHeineBorelSubcoverUp} :
    locatedHeineBorelSubcoverToEventFlow x =
      locatedHeineBorelSubcoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedHeineBorelSubcoverFromEventFlow
          (locatedHeineBorelSubcoverToEventFlow x) =
        locatedHeineBorelSubcoverFromEventFlow
          (locatedHeineBorelSubcoverToEventFlow y) :=
    congrArg locatedHeineBorelSubcoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_round_trip y)))

instance locatedHeineBorelSubcoverBHistCarrier :
    BHistCarrier LocatedHeineBorelSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedHeineBorelSubcoverToEventFlow
  fromEventFlow := locatedHeineBorelSubcoverFromEventFlow

instance locatedHeineBorelSubcoverChapterTasteGate :
    ChapterTasteGate LocatedHeineBorelSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedHeineBorelSubcoverFromEventFlow
        (locatedHeineBorelSubcoverToEventFlow x) = some x
    exact LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedHeineBorelSubcoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedHeineBorelSubcoverChapterTasteGate

theorem LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedHeineBorelSubcoverDecodeBHist
      (locatedHeineBorelSubcoverEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedHeineBorelSubcoverUp) ∧
        Nonempty (ChapterTasteGate LocatedHeineBorelSubcoverUp) ∧
          locatedHeineBorelSubcoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedHeineBorelSubcoverTasteGate_single_carrier_alignment_decode_encode,
      ⟨locatedHeineBorelSubcoverBHistCarrier⟩,
      ⟨locatedHeineBorelSubcoverChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedHeineBorelSubcoverUp
