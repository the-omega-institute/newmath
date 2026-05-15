import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HashLikeFiberBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HashLikeFiberBoundaryUp : Type where
  | mk (digest fiber gap farEnd refusal transport route provenance nameRow : BHist) :
      HashLikeFiberBoundaryUp
  deriving DecidableEq

def hashLikeFiberBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hashLikeFiberBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hashLikeFiberBoundaryEncodeBHist h

def hashLikeFiberBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hashLikeFiberBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hashLikeFiberBoundaryDecodeBHist tail)

private theorem hashLikeFiberBoundaryDecode_encode_bhist :
    ∀ h : BHist, hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hashLikeFiberBoundaryToEventFlow : HashLikeFiberBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HashLikeFiberBoundaryUp.mk digest fiber gap farEnd refusal transport route provenance nameRow =>
      [[BMark.b0],
        hashLikeFiberBoundaryEncodeBHist digest,
        [BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist fiber,
        [BMark.b1, BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist farEnd,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hashLikeFiberBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hashLikeFiberBoundaryEncodeBHist nameRow]

def hashLikeFiberBoundaryFromEventFlow : EventFlow → Option HashLikeFiberBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | digest :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | fiber :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | farEnd :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameRow :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HashLikeFiberBoundaryUp.mk
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    digest)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    fiber)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    gap)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    farEnd)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    refusal)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    route)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (hashLikeFiberBoundaryDecodeBHist
                                                                                    nameRow))
                                                                          | _ :: _ => none

private theorem hashLikeFiberBoundary_round_trip :
    ∀ x : HashLikeFiberBoundaryUp,
      hashLikeFiberBoundaryFromEventFlow (hashLikeFiberBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk digest fiber gap farEnd refusal transport route provenance nameRow =>
      change
        some
          (HashLikeFiberBoundaryUp.mk
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist digest))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist fiber))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist gap))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist farEnd))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist refusal))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist transport))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist route))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist provenance))
            (hashLikeFiberBoundaryDecodeBHist (hashLikeFiberBoundaryEncodeBHist nameRow))) =
          some
            (HashLikeFiberBoundaryUp.mk digest fiber gap farEnd refusal transport route
              provenance nameRow)
      rw [hashLikeFiberBoundaryDecode_encode_bhist digest,
        hashLikeFiberBoundaryDecode_encode_bhist fiber,
        hashLikeFiberBoundaryDecode_encode_bhist gap,
        hashLikeFiberBoundaryDecode_encode_bhist farEnd,
        hashLikeFiberBoundaryDecode_encode_bhist refusal,
        hashLikeFiberBoundaryDecode_encode_bhist transport,
        hashLikeFiberBoundaryDecode_encode_bhist route,
        hashLikeFiberBoundaryDecode_encode_bhist provenance,
        hashLikeFiberBoundaryDecode_encode_bhist nameRow]

private theorem hashLikeFiberBoundaryToEventFlow_injective {x y : HashLikeFiberBoundaryUp} :
    hashLikeFiberBoundaryToEventFlow x = hashLikeFiberBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hashLikeFiberBoundaryFromEventFlow (hashLikeFiberBoundaryToEventFlow x) =
        hashLikeFiberBoundaryFromEventFlow (hashLikeFiberBoundaryToEventFlow y) :=
    congrArg hashLikeFiberBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hashLikeFiberBoundary_round_trip x).symm
      (Eq.trans hread (hashLikeFiberBoundary_round_trip y)))

instance hashLikeFiberBoundaryBHistCarrier : BHistCarrier HashLikeFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hashLikeFiberBoundaryToEventFlow
  fromEventFlow := hashLikeFiberBoundaryFromEventFlow

instance hashLikeFiberBoundaryChapterTasteGate : ChapterTasteGate HashLikeFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hashLikeFiberBoundaryFromEventFlow (hashLikeFiberBoundaryToEventFlow x) = some x
    exact hashLikeFiberBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hashLikeFiberBoundaryToEventFlow_injective heq)

instance hashLikeFiberBoundaryFieldFaithful : FieldFaithful HashLikeFiberBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | HashLikeFiberBoundaryUp.mk digest fiber gap farEnd refusal transport route provenance
        nameRow =>
        [digest, fiber, gap, farEnd, refusal, transport, route, provenance, nameRow]
  field_faithful := by
    intro x y h
    cases x with
    | mk digest₁ fiber₁ gap₁ farEnd₁ refusal₁ transport₁ route₁ provenance₁ nameRow₁ =>
        cases y with
        | mk digest₂ fiber₂ gap₂ farEnd₂ refusal₂ transport₂ route₂ provenance₂ nameRow₂ =>
            simp only [] at h
            cases h
            rfl

end BEDC.Derived.HashLikeFiberBoundaryUp
