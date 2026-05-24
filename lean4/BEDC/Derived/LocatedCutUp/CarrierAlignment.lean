import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive LocatedCutUp : Type where
  | mk (lower upper window handoff sealRow transport replay provenance localCert : BHist) :
      LocatedCutUp
  deriving DecidableEq

def locatedCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCutEncodeBHist h

def locatedCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCutDecodeBHist tail)

private theorem LocatedCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedCutDecodeBHist (locatedCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCutFields : LocatedCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCutUp.mk lower upper window handoff sealRow transport replay provenance localCert =>
      [lower, upper, window, handoff, sealRow, transport, replay, provenance, localCert]

def locatedCutToEventFlow : LocatedCutUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCutFields x).map locatedCutEncodeBHist

def locatedCutFromEventFlow : EventFlow → Option LocatedCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | handoff :: rest3 =>
                  match rest3 with
                  | [] => none
                  | sealRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (LocatedCutUp.mk
                                              (locatedCutDecodeBHist lower)
                                              (locatedCutDecodeBHist upper)
                                              (locatedCutDecodeBHist window)
                                              (locatedCutDecodeBHist handoff)
                                              (locatedCutDecodeBHist sealRow)
                                              (locatedCutDecodeBHist transport)
                                              (locatedCutDecodeBHist replay)
                                              (locatedCutDecodeBHist provenance)
                                              (locatedCutDecodeBHist localCert))
                                      | _ :: _ => none

theorem LocatedCutTasteGate_single_carrier_alignment_round_trip
    (x : LocatedCutUp) :
    locatedCutFromEventFlow (locatedCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk lower upper window handoff sealRow transport replay provenance localCert =>
      change
        some
          (LocatedCutUp.mk
            (locatedCutDecodeBHist (locatedCutEncodeBHist lower))
            (locatedCutDecodeBHist (locatedCutEncodeBHist upper))
            (locatedCutDecodeBHist (locatedCutEncodeBHist window))
            (locatedCutDecodeBHist (locatedCutEncodeBHist handoff))
            (locatedCutDecodeBHist (locatedCutEncodeBHist sealRow))
            (locatedCutDecodeBHist (locatedCutEncodeBHist transport))
            (locatedCutDecodeBHist (locatedCutEncodeBHist replay))
            (locatedCutDecodeBHist (locatedCutEncodeBHist provenance))
            (locatedCutDecodeBHist (locatedCutEncodeBHist localCert))) =
          some
            (LocatedCutUp.mk lower upper window handoff sealRow transport replay provenance
              localCert)
      rw [LocatedCutTasteGate_single_carrier_alignment_decode_encode lower,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode upper,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode window,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode handoff,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode sealRow,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode replay,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedCutTasteGate_single_carrier_alignment_decode_encode localCert]

theorem LocatedCutTasteGate_single_carrier_alignment_injective {x y : LocatedCutUp} :
    locatedCutToEventFlow x = locatedCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCutFromEventFlow (locatedCutToEventFlow x) =
        locatedCutFromEventFlow (locatedCutToEventFlow y) :=
    congrArg locatedCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCutTasteGate_single_carrier_alignment_round_trip y)))

theorem LocatedCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCutDecodeBHist (locatedCutEncodeBHist h) = h) ∧
      (∀ x : LocatedCutUp, locatedCutFromEventFlow (locatedCutToEventFlow x) = some x) ∧
        locatedCutEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedCutTasteGate_single_carrier_alignment_decode_encode,
      LocatedCutTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.LocatedCutUp
