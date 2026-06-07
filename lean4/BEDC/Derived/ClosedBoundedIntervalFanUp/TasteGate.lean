import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalFanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalFanUp : Type where
  | mk :
      (interval tree bar stability stream readback realSeal transport replay provenance
        localNameCert : BHist) ->
        ClosedBoundedIntervalFanUp
  deriving DecidableEq

def closedBoundedIntervalFanEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalFanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalFanEncodeBHist h

def closedBoundedIntervalFanDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalFanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalFanDecodeBHist tail)

theorem ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      closedBoundedIntervalFanDecodeBHist
          (closedBoundedIntervalFanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedBoundedIntervalFanFields : ClosedBoundedIntervalFanUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalFanUp.mk interval tree bar stability stream readback realSeal transport
      replay provenance localNameCert =>
      [interval, tree, bar, stability, stream, readback, realSeal, transport, replay, provenance,
        localNameCert]

def closedBoundedIntervalFanToEventFlow : ClosedBoundedIntervalFanUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedBoundedIntervalFanFields x).map closedBoundedIntervalFanEncodeBHist

def closedBoundedIntervalFanFromEventFlow : EventFlow -> Option ClosedBoundedIntervalFanUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | interval :: rest0 =>
      match rest0 with
      | [] => none
      | tree :: rest1 =>
          match rest1 with
          | [] => none
          | bar :: rest2 =>
              match rest2 with
              | [] => none
              | stability :: rest3 =>
                  match rest3 with
                  | [] => none
                  | stream :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localNameCert :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ClosedBoundedIntervalFanUp.mk
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        interval)
                                                      (closedBoundedIntervalFanDecodeBHist tree)
                                                      (closedBoundedIntervalFanDecodeBHist bar)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        stability)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        stream)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        readback)
                                                      (closedBoundedIntervalFanDecodeBHist realSeal)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        transport)
                                                      (closedBoundedIntervalFanDecodeBHist replay)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        provenance)
                                                      (closedBoundedIntervalFanDecodeBHist
                                                        localNameCert))
                                              | _ :: _ => none

theorem ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_round_trip :
    forall x : ClosedBoundedIntervalFanUp,
      closedBoundedIntervalFanFromEventFlow
          (closedBoundedIntervalFanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval tree bar stability stream readback realSeal transport replay provenance
      localNameCert =>
      change
        some
          (ClosedBoundedIntervalFanUp.mk
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist interval))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist tree))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist bar))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist stability))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist stream))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist readback))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist realSeal))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist transport))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist replay))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist provenance))
            (closedBoundedIntervalFanDecodeBHist
              (closedBoundedIntervalFanEncodeBHist localNameCert))) =
          some
            (ClosedBoundedIntervalFanUp.mk interval tree bar stability stream readback realSeal
              transport replay provenance localNameCert)
      rw [ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode interval,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode tree,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode bar,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode stability,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode stream,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode readback,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode realSeal,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode transport,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode replay,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode provenance,
        ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode localNameCert]

theorem ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedBoundedIntervalFanUp} :
    closedBoundedIntervalFanToEventFlow x = closedBoundedIntervalFanToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalFanFromEventFlow (closedBoundedIntervalFanToEventFlow x) =
        closedBoundedIntervalFanFromEventFlow (closedBoundedIntervalFanToEventFlow y) :=
    congrArg closedBoundedIntervalFanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_round_trip y)))

theorem ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_field_faithful :
    forall x y : ClosedBoundedIntervalFanUp,
      closedBoundedIntervalFanFields x = closedBoundedIntervalFanFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval₁ tree₁ bar₁ stability₁ stream₁ readback₁ realSeal₁ transport₁ replay₁
      provenance₁ localNameCert₁ =>
      cases y with
      | mk interval₂ tree₂ bar₂ stability₂ stream₂ readback₂ realSeal₂ transport₂ replay₂
          provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance closedBoundedIntervalFanBHistCarrier :
    BHistCarrier ClosedBoundedIntervalFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalFanToEventFlow
  fromEventFlow := closedBoundedIntervalFanFromEventFlow

instance closedBoundedIntervalFanChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance closedBoundedIntervalFanFieldFaithful :
    FieldFaithful ClosedBoundedIntervalFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedBoundedIntervalFanFields
  field_faithful :=
    ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_field_faithful

instance closedBoundedIntervalFanNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ClosedBoundedIntervalFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedBoundedIntervalFanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedBoundedIntervalFanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def closedBoundedIntervalFanTasteGate :
    ChapterTasteGate ClosedBoundedIntervalFanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedBoundedIntervalFanChapterTasteGate

theorem ClosedBoundedIntervalFanTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        closedBoundedIntervalFanDecodeBHist
          (closedBoundedIntervalFanEncodeBHist h) = h) ∧
      (∀ x : ClosedBoundedIntervalFanUp,
        closedBoundedIntervalFanFromEventFlow
          (closedBoundedIntervalFanToEventFlow x) = some x) ∧
        (∀ x y : ClosedBoundedIntervalFanUp,
          closedBoundedIntervalFanToEventFlow x =
              closedBoundedIntervalFanToEventFlow y ->
            x = y) ∧
          closedBoundedIntervalFanEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          ClosedBoundedIntervalFanTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedBoundedIntervalFanUp
