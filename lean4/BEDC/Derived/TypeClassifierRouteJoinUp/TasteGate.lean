import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# TypeClassifierRouteJoinUp TasteGate carrier.
-/

namespace BEDC.Derived.TypeClassifierRouteJoinUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite route-join token exposing the seven paper carrier rows. -/
inductive TypeClassifierRouteJoinUp : Type where
  | mk :
      (membership routeChoice dischargeSocket transports replay provenance localName
        joinedRead : BHist) →
      TypeClassifierRouteJoinUp
  deriving DecidableEq

def typeClassifierRouteJoinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeClassifierRouteJoinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeClassifierRouteJoinEncodeBHist h

private def typeClassifierRouteJoinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeClassifierRouteJoinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeClassifierRouteJoinDecodeBHist tail)

private theorem typeClassifierRouteJoin_decode_encode_bhist :
    ∀ h : BHist,
      typeClassifierRouteJoinDecodeBHist (typeClassifierRouteJoinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def typeClassifierRouteJoinToEventFlow :
    TypeClassifierRouteJoinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypeClassifierRouteJoinUp.mk membership routeChoice dischargeSocket transports replay
      provenance localName joinedRead =>
      [[BMark.b0],
        typeClassifierRouteJoinEncodeBHist membership,
        [BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist routeChoice,
        [BMark.b1, BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist dischargeSocket,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeClassifierRouteJoinEncodeBHist localName,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typeClassifierRouteJoinEncodeBHist joinedRead]

private def typeClassifierRouteJoinFromEventFlow :
    EventFlow → Option TypeClassifierRouteJoinUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | membership :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | routeChoice :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dischargeSocket :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transports :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
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
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | joinedRead :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TypeClassifierRouteJoinUp.mk
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            membership)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            routeChoice)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            dischargeSocket)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            transports)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            replay)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            provenance)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            localName)
                                                                          (typeClassifierRouteJoinDecodeBHist
                                                                            joinedRead))
                                                                  | _ :: _ => none

private theorem typeClassifierRouteJoin_round_trip :
    ∀ x : TypeClassifierRouteJoinUp,
      typeClassifierRouteJoinFromEventFlow (typeClassifierRouteJoinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk membership routeChoice dischargeSocket transports replay provenance localName
      joinedRead =>
      change
        some
          (TypeClassifierRouteJoinUp.mk
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist membership))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist routeChoice))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist dischargeSocket))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist transports))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist replay))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist provenance))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist localName))
            (typeClassifierRouteJoinDecodeBHist
              (typeClassifierRouteJoinEncodeBHist joinedRead))) =
          some
            (TypeClassifierRouteJoinUp.mk membership routeChoice dischargeSocket transports replay
              provenance localName joinedRead)
      rw [typeClassifierRouteJoin_decode_encode_bhist membership,
        typeClassifierRouteJoin_decode_encode_bhist routeChoice,
        typeClassifierRouteJoin_decode_encode_bhist dischargeSocket,
        typeClassifierRouteJoin_decode_encode_bhist transports,
        typeClassifierRouteJoin_decode_encode_bhist replay,
        typeClassifierRouteJoin_decode_encode_bhist provenance,
        typeClassifierRouteJoin_decode_encode_bhist localName,
        typeClassifierRouteJoin_decode_encode_bhist joinedRead]

private theorem typeClassifierRouteJoinToEventFlow_injective
    {x y : TypeClassifierRouteJoinUp} :
    typeClassifierRouteJoinToEventFlow x = typeClassifierRouteJoinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeClassifierRouteJoinFromEventFlow (typeClassifierRouteJoinToEventFlow x) =
        typeClassifierRouteJoinFromEventFlow (typeClassifierRouteJoinToEventFlow y) :=
    congrArg typeClassifierRouteJoinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typeClassifierRouteJoin_round_trip x).symm
      (Eq.trans hread (typeClassifierRouteJoin_round_trip y)))

instance typeClassifierRouteJoinBHistCarrier :
    BHistCarrier TypeClassifierRouteJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeClassifierRouteJoinToEventFlow
  fromEventFlow := typeClassifierRouteJoinFromEventFlow

instance typeClassifierRouteJoinChapterTasteGate :
    ChapterTasteGate TypeClassifierRouteJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typeClassifierRouteJoinFromEventFlow
        (typeClassifierRouteJoinToEventFlow x) = some x
    exact typeClassifierRouteJoin_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typeClassifierRouteJoinToEventFlow_injective heq)

instance typeClassifierRouteJoinFieldFaithful : FieldFaithful TypeClassifierRouteJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TypeClassifierRouteJoinUp.mk membership routeChoice dischargeSocket transports replay
        provenance localName joinedRead =>
        [membership, routeChoice, dischargeSocket, transports, replay, provenance, localName,
          joinedRead]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk membership₁ routeChoice₁ dischargeSocket₁ transports₁ replay₁ provenance₁
        localName₁ joinedRead₁ =>
        cases y with
        | mk membership₂ routeChoice₂ dischargeSocket₂ transports₂ replay₂ provenance₂
            localName₂ joinedRead₂ =>
            simp only [] at h
            cases h
            rfl

instance typeClassifierRouteJoinNontrivial : Nontrivial TypeClassifierRouteJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypeClassifierRouteJoinUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypeClassifierRouteJoinUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TypeClassifierRouteJoinUp_single_carrier_alignment :
    (∀ h : BHist,
      typeClassifierRouteJoinDecodeBHist (typeClassifierRouteJoinEncodeBHist h) = h) ∧
      (∀ x : TypeClassifierRouteJoinUp,
        typeClassifierRouteJoinFromEventFlow (typeClassifierRouteJoinToEventFlow x) = some x) ∧
        (∀ x y : TypeClassifierRouteJoinUp,
          typeClassifierRouteJoinToEventFlow x = typeClassifierRouteJoinToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact typeClassifierRouteJoin_decode_encode_bhist
  · constructor
    · exact typeClassifierRouteJoin_round_trip
    · intro x y heq
      exact typeClassifierRouteJoinToEventFlow_injective heq

theorem TypeClassifierRouteJoinUp_nonescape (x : TypeClassifierRouteJoinUp) :
    (∃ membership routeChoice dischargeSocket transports replay provenance localName
        joinedRead : BHist,
      x =
          TypeClassifierRouteJoinUp.mk membership routeChoice dischargeSocket transports replay
            provenance localName joinedRead ∧
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ w m, List.Mem w (BHistCarrier.toEventFlow x) -> List.Mem m w ->
        m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · cases x with
    | mk membership routeChoice dischargeSocket transports replay provenance localName
        joinedRead =>
        exact
          ⟨membership, routeChoice, dischargeSocket, transports, replay, provenance,
            localName, joinedRead, rfl, ChapterTasteGate.round_trip _⟩
  · intro w m hw hm
    exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

end BEDC.Derived.TypeClassifierRouteJoinUp
