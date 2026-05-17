import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedBetaComparisonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedBetaComparisonUp : Type where
  | mk : (f t u nt nu e wt wu h c p n : BHist) → BoundedBetaComparisonUp
  deriving DecidableEq

def boundedBetaComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedBetaComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedBetaComparisonEncodeBHist h

def boundedBetaComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedBetaComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedBetaComparisonDecodeBHist tail)

theorem BoundedBetaComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedBetaComparisonToEventFlow : BoundedBetaComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedBetaComparisonUp.mk f t u nt nu e wt wu h c p n =>
      [[BMark.b0],
        boundedBetaComparisonEncodeBHist f,
        [BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist t,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist u,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist nt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist nu,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist wt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedBetaComparisonEncodeBHist wu,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedBetaComparisonEncodeBHist n]

def boundedBetaComparisonFromEventFlow : EventFlow → Option BoundedBetaComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | f :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | t :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | u :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | nt :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nu :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | e :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | wt :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | wu :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | h :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | c :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | p :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | n :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (BoundedBetaComparisonUp.mk
                                                                                                          (boundedBetaComparisonDecodeBHist f)
                                                                                                          (boundedBetaComparisonDecodeBHist t)
                                                                                                          (boundedBetaComparisonDecodeBHist u)
                                                                                                          (boundedBetaComparisonDecodeBHist nt)
                                                                                                          (boundedBetaComparisonDecodeBHist nu)
                                                                                                          (boundedBetaComparisonDecodeBHist e)
                                                                                                          (boundedBetaComparisonDecodeBHist wt)
                                                                                                          (boundedBetaComparisonDecodeBHist wu)
                                                                                                          (boundedBetaComparisonDecodeBHist h)
                                                                                                          (boundedBetaComparisonDecodeBHist c)
                                                                                                          (boundedBetaComparisonDecodeBHist p)
                                                                                                          (boundedBetaComparisonDecodeBHist n))
                                                                                                  | _ :: _ => none

theorem BoundedBetaComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedBetaComparisonUp,
      boundedBetaComparisonFromEventFlow (boundedBetaComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk f t u nt nu e wt wu h c p n =>
      change
        some
          (BoundedBetaComparisonUp.mk
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist f))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist t))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist u))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist nt))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist nu))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist e))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist wt))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist wu))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist h))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist c))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist p))
            (boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist n))) =
          some (BoundedBetaComparisonUp.mk f t u nt nu e wt wu h c p n)
      rw [BoundedBetaComparisonTasteGate_single_carrier_alignment_decode f,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode t,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode u,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode nt,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode nu,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode e,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode wt,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode wu,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode h,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode c,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode p,
        BoundedBetaComparisonTasteGate_single_carrier_alignment_decode n]

theorem BoundedBetaComparisonTasteGate_single_carrier_alignment_injective
    {x y : BoundedBetaComparisonUp} :
    boundedBetaComparisonToEventFlow x = boundedBetaComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedBetaComparisonFromEventFlow (boundedBetaComparisonToEventFlow x) =
        boundedBetaComparisonFromEventFlow (boundedBetaComparisonToEventFlow y) :=
    congrArg boundedBetaComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedBetaComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedBetaComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance boundedBetaComparisonBHistCarrier : BHistCarrier BoundedBetaComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedBetaComparisonToEventFlow
  fromEventFlow := boundedBetaComparisonFromEventFlow

instance boundedBetaComparisonChapterTasteGate : ChapterTasteGate BoundedBetaComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedBetaComparisonFromEventFlow (boundedBetaComparisonToEventFlow x) = some x
    exact BoundedBetaComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedBetaComparisonTasteGate_single_carrier_alignment_injective heq)

instance boundedBetaComparisonFieldFaithful : FieldFaithful BoundedBetaComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BoundedBetaComparisonUp.mk f t u nt nu e wt wu h c p n =>
        [f, t, u, nt, nu, e, wt, wu, h, c, p, n]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk f1 t1 u1 nt1 nu1 e1 wt1 wu1 h1 c1 p1 n1 =>
        cases y with
        | mk f2 t2 u2 nt2 nu2 e2 wt2 wu2 h2 c2 p2 n2 =>
            injection hfields with hf tail1
            cases hf
            injection tail1 with ht tail2
            cases ht
            injection tail2 with hu tail3
            cases hu
            injection tail3 with hnt tail4
            cases hnt
            injection tail4 with hnu tail5
            cases hnu
            injection tail5 with he tail6
            cases he
            injection tail6 with hwt tail7
            cases hwt
            injection tail7 with hwu tail8
            cases hwu
            injection tail8 with hh tail9
            cases hh
            injection tail9 with hc tail10
            cases hc
            injection tail10 with hp tail11
            cases hp
            injection tail11 with hn _
            cases hn
            rfl

instance boundedBetaComparisonNontrivial : Nontrivial BoundedBetaComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedBetaComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedBetaComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hf
        cases hf⟩

theorem BoundedBetaComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedBetaComparisonDecodeBHist (boundedBetaComparisonEncodeBHist h) = h) ∧
      (∀ x : BoundedBetaComparisonUp,
        boundedBetaComparisonFromEventFlow (boundedBetaComparisonToEventFlow x) = some x) ∧
        (∀ x y : BoundedBetaComparisonUp,
          boundedBetaComparisonToEventFlow x = boundedBetaComparisonToEventFlow y → x = y) ∧
          boundedBetaComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BoundedBetaComparisonTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BoundedBetaComparisonTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BoundedBetaComparisonTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.BoundedBetaComparisonUp.TasteGate
