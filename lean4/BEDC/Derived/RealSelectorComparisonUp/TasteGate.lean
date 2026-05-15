import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSelectorComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSelectorComparisonUp : Type where
  | mk :
      (d0 d1 t w r l a h c p n : BHist) →
      RealSelectorComparisonUp
  deriving DecidableEq

def realSelectorComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSelectorComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSelectorComparisonEncodeBHist h

def realSelectorComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSelectorComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSelectorComparisonDecodeBHist tail)

private theorem realSelectorComparisonDecode_encode_bhist :
    ∀ h : BHist,
      realSelectorComparisonDecodeBHist
        (realSelectorComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realSelectorComparison_mk_congr
    {d0 d0' d1 d1' t t' w w' r r' l l' a a' h h' c c' p p' n n' : BHist}
    (hd0 : d0' = d0)
    (hd1 : d1' = d1)
    (ht : t' = t)
    (hw : w' = w)
    (hr : r' = r)
    (hl : l' = l)
    (ha : a' = a)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hn : n' = n) :
    RealSelectorComparisonUp.mk d0' d1' t' w' r' l' a' h' c' p' n' =
      RealSelectorComparisonUp.mk d0 d1 t w r l a h c p n := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hd0
  cases hd1
  cases ht
  cases hw
  cases hr
  cases hl
  cases ha
  cases hh
  cases hc
  cases hp
  cases hn
  rfl

def realSelectorComparisonFields :
    RealSelectorComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSelectorComparisonUp.mk d0 d1 t w r l a h c p n =>
      [d0, d1, t, w, r, l, a, h, c, p, n]

def realSelectorComparisonToEventFlow :
    RealSelectorComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | pkt => (realSelectorComparisonFields pkt).map realSelectorComparisonEncodeBHist

def realSelectorComparisonFromEventFlow :
    EventFlow → Option RealSelectorComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | d0 :: rest0 =>
      match rest0 with
      | [] => none
      | d1 :: rest1 =>
          match rest1 with
          | [] => none
          | t :: rest2 =>
              match rest2 with
              | [] => none
              | w :: rest3 =>
                  match rest3 with
                  | [] => none
                  | r :: rest4 =>
                      match rest4 with
                      | [] => none
                      | l :: rest5 =>
                          match rest5 with
                          | [] => none
                          | a :: rest6 =>
                              match rest6 with
                              | [] => none
                              | h :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | c :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | p :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | n :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RealSelectorComparisonUp.mk
                                                      (realSelectorComparisonDecodeBHist d0)
                                                      (realSelectorComparisonDecodeBHist d1)
                                                      (realSelectorComparisonDecodeBHist t)
                                                      (realSelectorComparisonDecodeBHist w)
                                                      (realSelectorComparisonDecodeBHist r)
                                                      (realSelectorComparisonDecodeBHist l)
                                                      (realSelectorComparisonDecodeBHist a)
                                                      (realSelectorComparisonDecodeBHist h)
                                                      (realSelectorComparisonDecodeBHist c)
                                                      (realSelectorComparisonDecodeBHist p)
                                                      (realSelectorComparisonDecodeBHist n))
                                              | _ :: _ => none

private theorem realSelectorComparison_round_trip :
    ∀ pkt : RealSelectorComparisonUp,
      realSelectorComparisonFromEventFlow
        (realSelectorComparisonToEventFlow pkt) = some pkt := by
  -- BEDC touchpoint anchor: BHist BMark
  intro pkt
  cases pkt with
  | mk d0 d1 t w r l a h c p n =>
      change
        some
          (RealSelectorComparisonUp.mk
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist d0))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist d1))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist t))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist w))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist r))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist l))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist a))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist h))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist c))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist p))
            (realSelectorComparisonDecodeBHist (realSelectorComparisonEncodeBHist n))) =
          some (RealSelectorComparisonUp.mk d0 d1 t w r l a h c p n)
      exact
        congrArg some
          (realSelectorComparison_mk_congr
            (realSelectorComparisonDecode_encode_bhist d0)
            (realSelectorComparisonDecode_encode_bhist d1)
            (realSelectorComparisonDecode_encode_bhist t)
            (realSelectorComparisonDecode_encode_bhist w)
            (realSelectorComparisonDecode_encode_bhist r)
            (realSelectorComparisonDecode_encode_bhist l)
            (realSelectorComparisonDecode_encode_bhist a)
            (realSelectorComparisonDecode_encode_bhist h)
            (realSelectorComparisonDecode_encode_bhist c)
            (realSelectorComparisonDecode_encode_bhist p)
            (realSelectorComparisonDecode_encode_bhist n))

private theorem realSelectorComparisonToEventFlow_injective
    {x y : RealSelectorComparisonUp} :
    realSelectorComparisonToEventFlow x =
      realSelectorComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSelectorComparisonFromEventFlow
          (realSelectorComparisonToEventFlow x) =
        realSelectorComparisonFromEventFlow
          (realSelectorComparisonToEventFlow y) :=
    congrArg realSelectorComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSelectorComparison_round_trip x).symm
      (Eq.trans hread (realSelectorComparison_round_trip y)))

private theorem realSelectorComparison_fields_faithful :
    ∀ x y : RealSelectorComparisonUp,
      realSelectorComparisonFields x =
        realSelectorComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk d0₁ d1₁ t₁ w₁ r₁ l₁ a₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk d0₂ d1₂ t₂ w₂ r₂ l₂ a₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hd0 tail0
          injection tail0 with hd1 tail1
          injection tail1 with ht tail2
          injection tail2 with hw tail3
          injection tail3 with hr tail4
          injection tail4 with hl tail5
          injection tail5 with ha tail6
          injection tail6 with hh tail7
          injection tail7 with hc tail8
          injection tail8 with hp tail9
          injection tail9 with hn _
          subst hd0
          subst hd1
          subst ht
          subst hw
          subst hr
          subst hl
          subst ha
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance realSelectorComparisonBHistCarrier :
    BHistCarrier RealSelectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSelectorComparisonToEventFlow
  fromEventFlow := realSelectorComparisonFromEventFlow

instance realSelectorComparisonChapterTasteGate :
    ChapterTasteGate RealSelectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realSelectorComparisonFromEventFlow
        (realSelectorComparisonToEventFlow x) = some x
    exact realSelectorComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSelectorComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealSelectorComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSelectorComparisonChapterTasteGate

instance realSelectorComparisonFieldFaithful :
    FieldFaithful RealSelectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSelectorComparisonFields
  field_faithful := realSelectorComparison_fields_faithful

instance realSelectorComparisonNontrivial :
    Nontrivial RealSelectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSelectorComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealSelectorComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealSelectorComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realSelectorComparisonDecodeBHist
          (realSelectorComparisonEncodeBHist h) = h) ∧
      (∀ x : RealSelectorComparisonUp,
        realSelectorComparisonFromEventFlow
          (realSelectorComparisonToEventFlow x) = some x) ∧
        (∀ x y : RealSelectorComparisonUp,
          realSelectorComparisonToEventFlow x =
            realSelectorComparisonToEventFlow y → x = y) ∧
          realSelectorComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realSelectorComparisonDecode_encode_bhist
  · constructor
    · exact realSelectorComparison_round_trip
    · constructor
      · intro x y heq
        exact realSelectorComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSelectorComparisonUp
