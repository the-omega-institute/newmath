import BEDC.Derived.ZCarryUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZCarryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZCarryUp : Type where
  | mk
      (source target carryRoute sourceReadback targetReadback carryReadback nameCert : BHist) :
      ZCarryUp
  deriving DecidableEq

def zCarryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zCarryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zCarryEncodeBHist h

def zCarryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zCarryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zCarryDecodeBHist tail)

theorem ZCarryUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist, zCarryDecodeBHist (zCarryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

theorem ZCarryUp_single_carrier_alignment_mk_congr
    {source source' target target' carryRoute carryRoute' sourceReadback sourceReadback'
      targetReadback targetReadback' carryReadback carryReadback' nameCert nameCert' : BHist}
    (hSource : source' = source)
    (hTarget : target' = target)
    (hCarryRoute : carryRoute' = carryRoute)
    (hSourceReadback : sourceReadback' = sourceReadback)
    (hTargetReadback : targetReadback' = targetReadback)
    (hCarryReadback : carryReadback' = carryReadback)
    (hNameCert : nameCert' = nameCert) :
    ZCarryUp.mk source' target' carryRoute' sourceReadback' targetReadback' carryReadback'
        nameCert' =
      ZCarryUp.mk source target carryRoute sourceReadback targetReadback carryReadback
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hCarryRoute
  cases hSourceReadback
  cases hTargetReadback
  cases hCarryReadback
  cases hNameCert
  rfl

def zCarryToEventFlow : ZCarryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZCarryUp.mk source target carryRoute sourceReadback targetReadback carryReadback
      nameCert =>
      [zCarryEncodeBHist source,
        zCarryEncodeBHist target,
        zCarryEncodeBHist carryRoute,
        zCarryEncodeBHist sourceReadback,
        zCarryEncodeBHist targetReadback,
        zCarryEncodeBHist carryReadback,
        zCarryEncodeBHist nameCert]

def zCarryFromEventFlow : EventFlow → Option ZCarryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | carryRoute :: rest2 =>
              match rest2 with
              | [] => none
              | sourceReadback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | targetReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | carryReadback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | nameCert :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (ZCarryUp.mk
                                      (zCarryDecodeBHist source)
                                      (zCarryDecodeBHist target)
                                      (zCarryDecodeBHist carryRoute)
                                      (zCarryDecodeBHist sourceReadback)
                                      (zCarryDecodeBHist targetReadback)
                                      (zCarryDecodeBHist carryReadback)
                                      (zCarryDecodeBHist nameCert))
                              | _ :: _ => none

theorem ZCarryUp_single_carrier_alignment_round_trip :
    ∀ x : ZCarryUp, zCarryFromEventFlow (zCarryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target carryRoute sourceReadback targetReadback carryReadback nameCert =>
      change
        some
          (ZCarryUp.mk
            (zCarryDecodeBHist (zCarryEncodeBHist source))
            (zCarryDecodeBHist (zCarryEncodeBHist target))
            (zCarryDecodeBHist (zCarryEncodeBHist carryRoute))
            (zCarryDecodeBHist (zCarryEncodeBHist sourceReadback))
            (zCarryDecodeBHist (zCarryEncodeBHist targetReadback))
            (zCarryDecodeBHist (zCarryEncodeBHist carryReadback))
            (zCarryDecodeBHist (zCarryEncodeBHist nameCert))) =
          some
            (ZCarryUp.mk source target carryRoute sourceReadback targetReadback
              carryReadback nameCert)
      exact
        congrArg some
          (ZCarryUp_single_carrier_alignment_mk_congr
            (ZCarryUp_single_carrier_alignment_decode_encode source)
            (ZCarryUp_single_carrier_alignment_decode_encode target)
            (ZCarryUp_single_carrier_alignment_decode_encode carryRoute)
            (ZCarryUp_single_carrier_alignment_decode_encode sourceReadback)
            (ZCarryUp_single_carrier_alignment_decode_encode targetReadback)
            (ZCarryUp_single_carrier_alignment_decode_encode carryReadback)
            (ZCarryUp_single_carrier_alignment_decode_encode nameCert))

theorem ZCarryUp_single_carrier_alignment_toEventFlow_injective {x y : ZCarryUp} :
    zCarryToEventFlow x = zCarryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zCarryFromEventFlow (zCarryToEventFlow x) =
        zCarryFromEventFlow (zCarryToEventFlow y) :=
    congrArg zCarryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ZCarryUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ZCarryUp_single_carrier_alignment_round_trip y)))

instance zCarryBHistCarrier : BHistCarrier ZCarryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zCarryToEventFlow
  fromEventFlow := zCarryFromEventFlow

instance zCarryChapterTasteGate : ChapterTasteGate ZCarryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zCarryFromEventFlow (zCarryToEventFlow x) = some x
    exact ZCarryUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ZCarryUp_single_carrier_alignment_toEventFlow_injective heq)

theorem ZCarryUp_single_carrier_alignment :
    Nonempty (ChapterTasteGate ZCarryUp) ∧
      (∀ x : ZCarryUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        (∀ h : BHist, zCarryDecodeBHist (zCarryEncodeBHist h) = h) ∧
          zCarryEncodeBHist BHist.Empty = [] := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · exact ⟨zCarryChapterTasteGate⟩
  · constructor
    · intro x
      exact ⟨zCarryToEventFlow x, ZCarryUp_single_carrier_alignment_round_trip x⟩
    · constructor
      · exact ZCarryUp_single_carrier_alignment_decode_encode
      · rfl

end BEDC.Derived.ZCarryUp
