import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisNatReplacementRefusalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisNatReplacementRefusalUp : Type where
  | mk
      (axisNat nat bridge cannotClaim transports routes provenance name : BHist) :
      AxisNatReplacementRefusalUp
  deriving DecidableEq

def axisNatReplacementRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisNatReplacementRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisNatReplacementRefusalEncodeBHist h

def axisNatReplacementRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisNatReplacementRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisNatReplacementRefusalDecodeBHist tail)

private theorem axisNatReplacementRefusalDecode_encode_bhist :
    ∀ h : BHist,
      axisNatReplacementRefusalDecodeBHist
        (axisNatReplacementRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisNatReplacementRefusalToEventFlow : AxisNatReplacementRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisNatReplacementRefusalUp.mk axisNat nat bridge cannotClaim transports routes provenance
      name =>
      [[BMark.b0],
        axisNatReplacementRefusalEncodeBHist axisNat,
        [BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist nat,
        [BMark.b1, BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisNatReplacementRefusalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisNatReplacementRefusalEncodeBHist name]

def axisNatReplacementRefusalFromEventFlow :
    EventFlow → Option AxisNatReplacementRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | axisNat :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | nat :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | bridge :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | cannotClaim :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (AxisNatReplacementRefusalUp.mk
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            axisNat)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            nat)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            bridge)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            cannotClaim)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            transports)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            routes)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            provenance)
                                                                          (axisNatReplacementRefusalDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem axisNatReplacementRefusal_round_trip :
    ∀ x : AxisNatReplacementRefusalUp,
      axisNatReplacementRefusalFromEventFlow
        (axisNatReplacementRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk axisNat nat bridge cannotClaim transports routes provenance name =>
      change
        some
          (AxisNatReplacementRefusalUp.mk
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist axisNat))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist nat))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist bridge))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist cannotClaim))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist transports))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist routes))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist provenance))
            (axisNatReplacementRefusalDecodeBHist
              (axisNatReplacementRefusalEncodeBHist name))) =
          some
            (AxisNatReplacementRefusalUp.mk axisNat nat bridge cannotClaim transports routes
              provenance name)
      rw [axisNatReplacementRefusalDecode_encode_bhist axisNat,
        axisNatReplacementRefusalDecode_encode_bhist nat,
        axisNatReplacementRefusalDecode_encode_bhist bridge,
        axisNatReplacementRefusalDecode_encode_bhist cannotClaim,
        axisNatReplacementRefusalDecode_encode_bhist transports,
        axisNatReplacementRefusalDecode_encode_bhist routes,
        axisNatReplacementRefusalDecode_encode_bhist provenance,
        axisNatReplacementRefusalDecode_encode_bhist name]

private theorem axisNatReplacementRefusalToEventFlow_injective
    {x y : AxisNatReplacementRefusalUp} :
    axisNatReplacementRefusalToEventFlow x =
      axisNatReplacementRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisNatReplacementRefusalFromEventFlow
          (axisNatReplacementRefusalToEventFlow x) =
        axisNatReplacementRefusalFromEventFlow
          (axisNatReplacementRefusalToEventFlow y) :=
    congrArg axisNatReplacementRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisNatReplacementRefusal_round_trip x).symm
      (Eq.trans hread (axisNatReplacementRefusal_round_trip y)))

instance axisNatReplacementRefusalBHistCarrier :
    BHistCarrier AxisNatReplacementRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisNatReplacementRefusalToEventFlow
  fromEventFlow := axisNatReplacementRefusalFromEventFlow

instance axisNatReplacementRefusalChapterTasteGate :
    ChapterTasteGate AxisNatReplacementRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axisNatReplacementRefusalFromEventFlow
        (axisNatReplacementRefusalToEventFlow x) = some x
    exact axisNatReplacementRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisNatReplacementRefusalToEventFlow_injective heq)

instance axisNatReplacementRefusalFieldFaithful :
    FieldFaithful AxisNatReplacementRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun
    | AxisNatReplacementRefusalUp.mk axisNat nat bridge cannotClaim transports routes
        provenance name =>
        [axisNat, nat, bridge, cannotClaim, transports, routes, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk axisNat₁ nat₁ bridge₁ cannotClaim₁ transports₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk axisNat₂ nat₂ bridge₂ cannotClaim₂ transports₂ routes₂ provenance₂ name₂ =>
            cases hfields
            rfl

instance axisNatReplacementRefusalNontrivial :
    Nontrivial AxisNatReplacementRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisNatReplacementRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisNatReplacementRefusalUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AxisNatReplacementRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      axisNatReplacementRefusalDecodeBHist (axisNatReplacementRefusalEncodeBHist h) = h) ∧
      (∀ x : AxisNatReplacementRefusalUp,
        axisNatReplacementRefusalFromEventFlow
          (axisNatReplacementRefusalToEventFlow x) = some x) ∧
        (∀ x y : AxisNatReplacementRefusalUp,
          axisNatReplacementRefusalToEventFlow x =
            axisNatReplacementRefusalToEventFlow y → x = y) ∧
          axisNatReplacementRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axisNatReplacementRefusalDecode_encode_bhist
  · constructor
    · exact axisNatReplacementRefusal_round_trip
    · constructor
      · intro x y heq
        exact axisNatReplacementRefusalToEventFlow_injective heq
      · rfl

theorem AxisNatReplacementRefusalCarrier_namecert_obligations
    (q : AxisNatReplacementRefusalUp) :
    ∃ A N B K H C P L : BHist,
      q = AxisNatReplacementRefusalUp.mk A N B K H C P L ∧
        axisNatReplacementRefusalEncodeBHist BHist.Empty = ([] : List BMark) ∧
          axisNatReplacementRefusalFromEventFlow
            (axisNatReplacementRefusalToEventFlow q) = some q := by
  -- BEDC touchpoint anchor: BHist BMark
  cases q with
  | mk A N B K H C P L =>
      refine ⟨A, N, B, K, H, C, P, L, rfl, rfl, ?_⟩
      exact
        (AxisNatReplacementRefusalTasteGate_single_carrier_alignment).2.1
          (AxisNatReplacementRefusalUp.mk A N B K H C P L)

theorem AxisNatReplacementRefusalCarrier_nonreplacement_boundary
    {A N B K H C P L publicRead : BHist} :
    axisNatReplacementRefusalFromEventFlow
        (axisNatReplacementRefusalToEventFlow
          (AxisNatReplacementRefusalUp.mk A N B K H C P L)) =
      some (AxisNatReplacementRefusalUp.mk A N B K H C P L) →
      Cont K H publicRead →
        hsame publicRead (append K H) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro accepted route
  exact route

end BEDC.Derived.AxisNatReplacementRefusalUp
