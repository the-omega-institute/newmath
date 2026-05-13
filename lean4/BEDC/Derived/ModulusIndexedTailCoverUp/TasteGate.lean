import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusIndexedTailCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusIndexedTailCoverUp : Type where
  | mk : (e m w t d r s h c p n : BHist) → ModulusIndexedTailCoverUp
  deriving DecidableEq

def modulusIndexedTailCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusIndexedTailCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusIndexedTailCoverEncodeBHist h

def modulusIndexedTailCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusIndexedTailCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusIndexedTailCoverDecodeBHist tail)

private theorem modulusIndexedTailCoverDecode_encode_bhist :
    ∀ h : BHist,
      modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem modulusIndexedTailCover_mk_congr
    {e e' m m' w w' t t' d d' r r' s s' h h' c c' p p' n n' : BHist}
    (he : e' = e)
    (hm : m' = m)
    (hw : w' = w)
    (ht : t' = t)
    (hd : d' = d)
    (hr : r' = r)
    (hs : s' = s)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hn : n' = n) :
    ModulusIndexedTailCoverUp.mk e' m' w' t' d' r' s' h' c' p' n' =
      ModulusIndexedTailCoverUp.mk e m w t d r s h c p n := by
  -- BEDC touchpoint anchor: BHist BMark
  cases he
  cases hm
  cases hw
  cases ht
  cases hd
  cases hr
  cases hs
  cases hh
  cases hc
  cases hp
  cases hn
  rfl

def modulusIndexedTailCoverToEventFlow : ModulusIndexedTailCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusIndexedTailCoverUp.mk e m w t d r s h c p n =>
      [[BMark.b0],
        modulusIndexedTailCoverEncodeBHist e,
        [BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist m,
        [BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist t,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modulusIndexedTailCoverEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedTailCoverEncodeBHist n]

def modulusIndexedTailCoverFromEventFlow : EventFlow → Option ModulusIndexedTailCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | e :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | m :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | w :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | t :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | d :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | r :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | s :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | h :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | c :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | p :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | n :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ModulusIndexedTailCoverUp.mk
                                                                                                  (modulusIndexedTailCoverDecodeBHist e)
                                                                                                  (modulusIndexedTailCoverDecodeBHist m)
                                                                                                  (modulusIndexedTailCoverDecodeBHist w)
                                                                                                  (modulusIndexedTailCoverDecodeBHist t)
                                                                                                  (modulusIndexedTailCoverDecodeBHist d)
                                                                                                  (modulusIndexedTailCoverDecodeBHist r)
                                                                                                  (modulusIndexedTailCoverDecodeBHist s)
                                                                                                  (modulusIndexedTailCoverDecodeBHist h)
                                                                                                  (modulusIndexedTailCoverDecodeBHist c)
                                                                                                  (modulusIndexedTailCoverDecodeBHist p)
                                                                                                  (modulusIndexedTailCoverDecodeBHist n))
                                                                                          | _ :: _ => none

private theorem modulusIndexedTailCover_round_trip :
    ∀ x : ModulusIndexedTailCoverUp,
      modulusIndexedTailCoverFromEventFlow (modulusIndexedTailCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk e m w t d r s h c p n =>
      change
        some
          (ModulusIndexedTailCoverUp.mk
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist e))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist m))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist w))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist t))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist d))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist r))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist s))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist h))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist c))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist p))
            (modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist n))) =
          some (ModulusIndexedTailCoverUp.mk e m w t d r s h c p n)
      exact
        congrArg some
          (modulusIndexedTailCover_mk_congr
            (modulusIndexedTailCoverDecode_encode_bhist e)
            (modulusIndexedTailCoverDecode_encode_bhist m)
            (modulusIndexedTailCoverDecode_encode_bhist w)
            (modulusIndexedTailCoverDecode_encode_bhist t)
            (modulusIndexedTailCoverDecode_encode_bhist d)
            (modulusIndexedTailCoverDecode_encode_bhist r)
            (modulusIndexedTailCoverDecode_encode_bhist s)
            (modulusIndexedTailCoverDecode_encode_bhist h)
            (modulusIndexedTailCoverDecode_encode_bhist c)
            (modulusIndexedTailCoverDecode_encode_bhist p)
            (modulusIndexedTailCoverDecode_encode_bhist n))

private theorem modulusIndexedTailCoverToEventFlow_injective {x y : ModulusIndexedTailCoverUp} :
    modulusIndexedTailCoverToEventFlow x = modulusIndexedTailCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusIndexedTailCoverFromEventFlow (modulusIndexedTailCoverToEventFlow x) =
        modulusIndexedTailCoverFromEventFlow (modulusIndexedTailCoverToEventFlow y) :=
    congrArg modulusIndexedTailCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modulusIndexedTailCover_round_trip x).symm
      (Eq.trans hread (modulusIndexedTailCover_round_trip y)))

instance modulusIndexedTailCoverBHistCarrier : BHistCarrier ModulusIndexedTailCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusIndexedTailCoverToEventFlow
  fromEventFlow := modulusIndexedTailCoverFromEventFlow

instance modulusIndexedTailCoverChapterTasteGate : ChapterTasteGate ModulusIndexedTailCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modulusIndexedTailCoverFromEventFlow (modulusIndexedTailCoverToEventFlow x) = some x
    exact modulusIndexedTailCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusIndexedTailCoverToEventFlow_injective heq)

theorem ModulusIndexedTailCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      modulusIndexedTailCoverDecodeBHist (modulusIndexedTailCoverEncodeBHist h) = h) ∧
      (∀ x : ModulusIndexedTailCoverUp,
        modulusIndexedTailCoverFromEventFlow (modulusIndexedTailCoverToEventFlow x) = some x) ∧
        (∀ x y : ModulusIndexedTailCoverUp,
          modulusIndexedTailCoverToEventFlow x = modulusIndexedTailCoverToEventFlow y → x = y) ∧
          modulusIndexedTailCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact modulusIndexedTailCoverDecode_encode_bhist
  · constructor
    · exact modulusIndexedTailCover_round_trip
    · constructor
      · intro x y heq
        exact modulusIndexedTailCoverToEventFlow_injective heq
      · rfl

end BEDC.Derived.ModulusIndexedTailCoverUp
