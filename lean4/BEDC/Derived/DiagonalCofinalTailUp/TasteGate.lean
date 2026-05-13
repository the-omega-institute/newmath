import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalCofinalTailUp : Type where
  | mk :
      (q s g d r w h c p n : BHist) →
        DiagonalCofinalTailUp
  deriving DecidableEq

def diagonalCofinalTailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalCofinalTailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalCofinalTailEncodeBHist h

def diagonalCofinalTailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalCofinalTailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalCofinalTailDecodeBHist tail)

private theorem diagonalCofinalTailDecode_encode_bhist :
    ∀ h : BHist,
      diagonalCofinalTailDecodeBHist
        (diagonalCofinalTailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diagonalCofinalTailToEventFlow :
    DiagonalCofinalTailUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalCofinalTailUp.mk q s g d r w h c p n =>
      [[BMark.b0],
        diagonalCofinalTailEncodeBHist q,
        [BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist g,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalCofinalTailEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        diagonalCofinalTailEncodeBHist n]

def diagonalCofinalTailFromEventFlow :
    EventFlow → Option DiagonalCofinalTailUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | s :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | g :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | d :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | r :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | w :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | h :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | c :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | p :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | n ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (DiagonalCofinalTailUp.mk
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            q)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            s)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            g)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            d)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            r)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            w)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            h)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            c)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            p)
                                                                                          (diagonalCofinalTailDecodeBHist
                                                                                            n))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem diagonalCofinalTail_round_trip :
    ∀ x : DiagonalCofinalTailUp,
      diagonalCofinalTailFromEventFlow
        (diagonalCofinalTailToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q s g d r w h c p n =>
      change
        some
          (DiagonalCofinalTailUp.mk
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist q))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist s))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist g))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist d))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist r))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist w))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist h))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist c))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist p))
            (diagonalCofinalTailDecodeBHist (diagonalCofinalTailEncodeBHist n))) =
          some (DiagonalCofinalTailUp.mk q s g d r w h c p n)
      rw [diagonalCofinalTailDecode_encode_bhist q,
        diagonalCofinalTailDecode_encode_bhist s,
        diagonalCofinalTailDecode_encode_bhist g,
        diagonalCofinalTailDecode_encode_bhist d,
        diagonalCofinalTailDecode_encode_bhist r,
        diagonalCofinalTailDecode_encode_bhist w,
        diagonalCofinalTailDecode_encode_bhist h,
        diagonalCofinalTailDecode_encode_bhist c,
        diagonalCofinalTailDecode_encode_bhist p,
        diagonalCofinalTailDecode_encode_bhist n]

private theorem diagonalCofinalTailToEventFlow_injective
    {x y : DiagonalCofinalTailUp} :
    diagonalCofinalTailToEventFlow x =
      diagonalCofinalTailToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalCofinalTailFromEventFlow (diagonalCofinalTailToEventFlow x) =
        diagonalCofinalTailFromEventFlow (diagonalCofinalTailToEventFlow y) :=
    congrArg diagonalCofinalTailFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalCofinalTail_round_trip x).symm
      (Eq.trans hread (diagonalCofinalTail_round_trip y)))

instance diagonalCofinalTailBHistCarrier :
    BHistCarrier DiagonalCofinalTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalCofinalTailToEventFlow
  fromEventFlow := diagonalCofinalTailFromEventFlow

instance diagonalCofinalTailChapterTasteGate :
    ChapterTasteGate DiagonalCofinalTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diagonalCofinalTailFromEventFlow
        (diagonalCofinalTailToEventFlow x) = some x
    exact diagonalCofinalTail_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalCofinalTailToEventFlow_injective heq)

instance diagonalCofinalTailFieldFaithful : FieldFaithful DiagonalCofinalTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DiagonalCofinalTailUp.mk q s g d r w h c p n => [q, s, g, d, r, w, h, c, p, n]
  field_faithful := by
    intro x y h
    cases x with
    | mk q₁ s₁ g₁ d₁ r₁ w₁ h₁ c₁ p₁ n₁ =>
        cases y with
        | mk q₂ s₂ g₂ d₂ r₂ w₂ h₂ c₂ p₂ n₂ =>
            cases h
            rfl

def taste_gate : ChapterTasteGate DiagonalCofinalTailUp :=
  diagonalCofinalTailChapterTasteGate

theorem DiagonalCofinalTailTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalCofinalTailDecodeBHist
      (diagonalCofinalTailEncodeBHist h) = h) ∧
      (∀ x : DiagonalCofinalTailUp,
        diagonalCofinalTailFromEventFlow
          (diagonalCofinalTailToEventFlow x) = some x) ∧
        (∀ x y : DiagonalCofinalTailUp,
          diagonalCofinalTailToEventFlow x =
            diagonalCofinalTailToEventFlow y → x = y) ∧
          diagonalCofinalTailEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalCofinalTailDecode_encode_bhist
  · constructor
    · exact diagonalCofinalTail_round_trip
    · constructor
      · intro x y heq
        exact diagonalCofinalTailToEventFlow_injective heq
      · rfl

end BEDC.Derived.DiagonalCofinalTailUp
