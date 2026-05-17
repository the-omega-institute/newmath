import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalCanonicityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalCanonicityUp : Type where
  | mk : (t l b f e h c p n : BHist) → ClosedNormalCanonicityUp
  deriving DecidableEq

def closedNormalCanonicityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalCanonicityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalCanonicityEncodeBHist h

def closedNormalCanonicityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalCanonicityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalCanonicityDecodeBHist tail)

theorem ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedNormalCanonicityToEventFlow : ClosedNormalCanonicityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalCanonicityUp.mk t l b f e h c p n =>
      [[BMark.b0],
        closedNormalCanonicityEncodeBHist t,
        [BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist l,
        [BMark.b1, BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist f,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedNormalCanonicityEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedNormalCanonicityEncodeBHist n]

def closedNormalCanonicityFromEventFlow : EventFlow → Option ClosedNormalCanonicityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | t :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | l :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | b :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | f :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | e :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | h :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | c :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | p :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | n :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ClosedNormalCanonicityUp.mk
                                                                                  (closedNormalCanonicityDecodeBHist t)
                                                                                  (closedNormalCanonicityDecodeBHist l)
                                                                                  (closedNormalCanonicityDecodeBHist b)
                                                                                  (closedNormalCanonicityDecodeBHist f)
                                                                                  (closedNormalCanonicityDecodeBHist e)
                                                                                  (closedNormalCanonicityDecodeBHist h)
                                                                                  (closedNormalCanonicityDecodeBHist c)
                                                                                  (closedNormalCanonicityDecodeBHist p)
                                                                                  (closedNormalCanonicityDecodeBHist n))
                                                                          | _ :: _ => none

theorem ClosedNormalCanonicityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedNormalCanonicityUp,
      closedNormalCanonicityFromEventFlow (closedNormalCanonicityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk t l b f e h c p n =>
      change
        some
          (ClosedNormalCanonicityUp.mk
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist t))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist l))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist b))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist f))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist e))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist h))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist c))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist p))
            (closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist n))) =
          some (ClosedNormalCanonicityUp.mk t l b f e h c p n)
      rw [ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode t,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode l,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode b,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode f,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode e,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode h,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode c,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode p,
        ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode n]

theorem ClosedNormalCanonicityTasteGate_single_carrier_alignment_injective
    {x y : ClosedNormalCanonicityUp} :
    closedNormalCanonicityToEventFlow x = closedNormalCanonicityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalCanonicityFromEventFlow (closedNormalCanonicityToEventFlow x) =
        closedNormalCanonicityFromEventFlow (closedNormalCanonicityToEventFlow y) :=
    congrArg closedNormalCanonicityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedNormalCanonicityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedNormalCanonicityTasteGate_single_carrier_alignment_round_trip y)))

instance closedNormalCanonicityBHistCarrier : BHistCarrier ClosedNormalCanonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalCanonicityToEventFlow
  fromEventFlow := closedNormalCanonicityFromEventFlow

instance closedNormalCanonicityChapterTasteGate : ChapterTasteGate ClosedNormalCanonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedNormalCanonicityFromEventFlow (closedNormalCanonicityToEventFlow x) = some x
    exact ClosedNormalCanonicityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedNormalCanonicityTasteGate_single_carrier_alignment_injective heq)

instance closedNormalCanonicityFieldFaithful : FieldFaithful ClosedNormalCanonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosedNormalCanonicityUp.mk t l b f e h c p n => [t, l, b, f, e, h, c, p, n]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk t1 l1 b1 f1 e1 h1 c1 p1 n1 =>
        cases y with
        | mk t2 l2 b2 f2 e2 h2 c2 p2 n2 =>
            injection hfields with ht tail1
            cases ht
            injection tail1 with hl tail2
            cases hl
            injection tail2 with hb tail3
            cases hb
            injection tail3 with hf tail4
            cases hf
            injection tail4 with he tail5
            cases he
            injection tail5 with hh tail6
            cases hh
            injection tail6 with hc tail7
            cases hc
            injection tail7 with hp tail8
            cases hp
            injection tail8 with hn _
            cases hn
            rfl

instance closedNormalCanonicityNontrivial : Nontrivial ClosedNormalCanonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedNormalCanonicityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedNormalCanonicityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with ht
        cases ht⟩

theorem ClosedNormalCanonicityTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedNormalCanonicityDecodeBHist (closedNormalCanonicityEncodeBHist h) = h) ∧
      (∀ x : ClosedNormalCanonicityUp,
        closedNormalCanonicityFromEventFlow (closedNormalCanonicityToEventFlow x) = some x) ∧
        (∀ x y : ClosedNormalCanonicityUp,
          closedNormalCanonicityToEventFlow x = closedNormalCanonicityToEventFlow y → x = y) ∧
          closedNormalCanonicityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ClosedNormalCanonicityTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ClosedNormalCanonicityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ClosedNormalCanonicityTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ClosedNormalCanonicityUp.TasteGate
