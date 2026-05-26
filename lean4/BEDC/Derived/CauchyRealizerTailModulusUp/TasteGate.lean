import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealizerTailModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealizerTailModulusUp : Type where
  | mk :
      (sharedTail schedule windows readbacks dyadicLedger realSeals transport replay provenance
        localName : BHist) ->
        CauchyRealizerTailModulusUp
  deriving DecidableEq

def CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist h

def CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist tail)

theorem CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
        (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fields :
    CauchyRealizerTailModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealizerTailModulusUp.mk sharedTail schedule windows readbacks dyadicLedger
      realSeals transport replay provenance localName =>
      [sharedTail, schedule, windows, readbacks, dyadicLedger, realSeals, transport,
        replay, provenance, localName]

def CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow :
    CauchyRealizerTailModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fields x).map
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist

def CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option CauchyRealizerTailModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sharedTail :: rest0 =>
      match rest0 with
      | [] => none
      | schedule :: rest1 =>
          match rest1 with
          | [] => none
          | windows :: rest2 =>
              match rest2 with
              | [] => none
              | readbacks :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeals :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyRealizerTailModulusUp.mk
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    sharedTail)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    schedule)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    windows)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    readbacks)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    dyadicLedger)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    realSeals)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    transport)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    replay)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    provenance)
                                                  (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
                                                    localName))
                                          | _ :: _ => none

theorem CauchyRealizerTailModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealizerTailModulusUp,
      CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sharedTail schedule windows readbacks dyadicLedger realSeals transport replay
      provenance localName =>
      change
        some
          (CauchyRealizerTailModulusUp.mk
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist sharedTail))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist schedule))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist windows))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist readbacks))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist dyadicLedger))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist realSeals))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist transport))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist replay))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist provenance))
            (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decodeBHist
              (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_encodeBHist localName))) =
          some
            (CauchyRealizerTailModulusUp.mk sharedTail schedule windows readbacks
              dyadicLedger realSeals transport replay provenance localName)
      rw [CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode sharedTail,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode schedule,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode windows,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode readbacks,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode realSeals,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_decode_encode localName]

theorem CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealizerTailModulusUp} :
    CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyRealizerTailModulusTasteGate_single_carrier_alignment_bHistCarrier :
    BHistCarrier CauchyRealizerTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyRealizerTailModulusTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyRealizerTailModulusTasteGate_single_carrier_alignment_chapterTasteGate :
    ChapterTasteGate CauchyRealizerTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRealizerTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyRealizerTailModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyRealizerTailModulusUp) ∧
      Nonempty (ChapterTasteGate CauchyRealizerTailModulusUp) ∧
      hsame BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro CauchyRealizerTailModulusTasteGate_single_carrier_alignment_bHistCarrier
  · constructor
    · exact Nonempty.intro CauchyRealizerTailModulusTasteGate_single_carrier_alignment_chapterTasteGate
    · exact hsame_refl BHist.Empty

end BEDC.Derived.CauchyRealizerTailModulusUp
