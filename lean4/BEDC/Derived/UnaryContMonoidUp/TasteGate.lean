import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnaryContMonoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnaryContMonoidUp : Type where
  | mk (unary operation unit transport coherence provenance namecert : BHist) :
      UnaryContMonoidUp
  deriving DecidableEq

def unaryContMonoidEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unaryContMonoidEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unaryContMonoidEncodeBHist h

def unaryContMonoidDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unaryContMonoidDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unaryContMonoidDecodeBHist tail)

private theorem unaryContMonoidDecode_encode_bhist :
    ∀ h : BHist, unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def unaryContMonoidToEventFlow : UnaryContMonoidUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryContMonoidUp.mk unary operation unit transport coherence provenance namecert =>
      [[BMark.b0],
        unaryContMonoidEncodeBHist unary,
        [BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist operation,
        [BMark.b1, BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist unit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist coherence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContMonoidEncodeBHist namecert]

def unaryContMonoidFromEventFlow : EventFlow → Option UnaryContMonoidUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | unary :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | operation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | unit :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | coherence :: rest9 =>
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
                                                      | namecert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (UnaryContMonoidUp.mk
                                                                  (unaryContMonoidDecodeBHist
                                                                    unary)
                                                                  (unaryContMonoidDecodeBHist
                                                                    operation)
                                                                  (unaryContMonoidDecodeBHist
                                                                    unit)
                                                                  (unaryContMonoidDecodeBHist
                                                                    transport)
                                                                  (unaryContMonoidDecodeBHist
                                                                    coherence)
                                                                  (unaryContMonoidDecodeBHist
                                                                    provenance)
                                                                  (unaryContMonoidDecodeBHist
                                                                    namecert))
                                                          | _ :: _ => none

private theorem unaryContMonoid_round_trip :
    ∀ x : UnaryContMonoidUp,
      unaryContMonoidFromEventFlow (unaryContMonoidToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk unary operation unit transport coherence provenance namecert =>
      change
        some
          (UnaryContMonoidUp.mk
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist unary))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist operation))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist unit))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist transport))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist coherence))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist provenance))
            (unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist namecert))) =
          some
            (UnaryContMonoidUp.mk unary operation unit transport coherence provenance
              namecert)
      rw [unaryContMonoidDecode_encode_bhist unary,
        unaryContMonoidDecode_encode_bhist operation,
        unaryContMonoidDecode_encode_bhist unit,
        unaryContMonoidDecode_encode_bhist transport,
        unaryContMonoidDecode_encode_bhist coherence,
        unaryContMonoidDecode_encode_bhist provenance,
        unaryContMonoidDecode_encode_bhist namecert]

private theorem unaryContMonoidToEventFlow_injective {x y : UnaryContMonoidUp} :
    unaryContMonoidToEventFlow x = unaryContMonoidToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unaryContMonoidFromEventFlow (unaryContMonoidToEventFlow x) =
        unaryContMonoidFromEventFlow (unaryContMonoidToEventFlow y) :=
    congrArg unaryContMonoidFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unaryContMonoid_round_trip x).symm
      (Eq.trans hread (unaryContMonoid_round_trip y)))

instance unaryContMonoidBHistCarrier : BHistCarrier UnaryContMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unaryContMonoidToEventFlow
  fromEventFlow := unaryContMonoidFromEventFlow

instance unaryContMonoidChapterTasteGate : ChapterTasteGate UnaryContMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change unaryContMonoidFromEventFlow (unaryContMonoidToEventFlow x) = some x
    exact unaryContMonoid_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unaryContMonoidToEventFlow_injective heq)

theorem UnaryContMonoidTasteGate_single_carrier_alignment :
    (∀ h : BHist, unaryContMonoidDecodeBHist (unaryContMonoidEncodeBHist h) = h) ∧
      (∀ x : UnaryContMonoidUp,
        unaryContMonoidFromEventFlow (unaryContMonoidToEventFlow x) = some x) ∧
      (∀ x y : UnaryContMonoidUp,
        unaryContMonoidToEventFlow x = unaryContMonoidToEventFlow y → x = y) ∧
      unaryContMonoidEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact unaryContMonoidDecode_encode_bhist
  · constructor
    · exact unaryContMonoid_round_trip
    · constructor
      · intro x y heq
        exact unaryContMonoidToEventFlow_injective heq
      · rfl

end BEDC.Derived.UnaryContMonoidUp
