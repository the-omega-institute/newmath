import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrefixTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrefixTreeUp : Type where
  | mk (V E F W H C P N : BHist) : PrefixTreeUp
  deriving DecidableEq

def prefixTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: prefixTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: prefixTreeEncodeBHist h

def prefixTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (prefixTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (prefixTreeDecodeBHist tail)

private theorem prefixTree_decode_encode_bhist :
    ∀ h : BHist, prefixTreeDecodeBHist (prefixTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem prefixTree_mk_congr
    {V V' E E' F F' W W' H H' C C' P P' N N' : BHist}
    (hV : V' = V) (hE : E' = E) (hF : F' = F) (hW : W' = W)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    PrefixTreeUp.mk V' E' F' W' H' C' P' N' =
      PrefixTreeUp.mk V E F W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hV
  cases hE
  cases hF
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def prefixTreeFields : PrefixTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrefixTreeUp.mk V E F W H C P N => [V, E, F, W, H, C, P, N]

def prefixTreeToEventFlow : PrefixTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PrefixTreeUp.mk V E F W H C P N =>
      [[BMark.b0],
        prefixTreeEncodeBHist V,
        [BMark.b1, BMark.b0],
        prefixTreeEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        prefixTreeEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixTreeEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixTreeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixTreeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixTreeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        prefixTreeEncodeBHist N]

def prefixTreeFromEventFlow : EventFlow → Option PrefixTreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagV :: restV =>
      match restV with
      | [] => none
      | V :: restE =>
          match restE with
          | [] => none
          | _tagE :: restF =>
              match restF with
              | [] => none
              | E :: restW =>
                  match restW with
                  | [] => none
                  | _tagF :: restH =>
                      match restH with
                      | [] => none
                      | F :: restC =>
                          match restC with
                          | [] => none
                          | _tagW :: restP =>
                              match restP with
                              | [] => none
                              | W :: restN =>
                                  match restN with
                                  | [] =>
                                      none
                                  | _tagH :: restHrow =>
                                      match restHrow with
                                      | [] => none
                                      | H :: restCtag =>
                                          match restCtag with
                                          | [] => none
                                          | _tagC :: restCrow =>
                                              match restCrow with
                                              | [] => none
                                              | C :: restPtag =>
                                                  match restPtag with
                                                  | [] => none
                                                  | _tagP :: restProw =>
                                                      match restProw with
                                                      | [] => none
                                                      | P :: restNtag =>
                                                          match restNtag with
                                                          | [] => none
                                                          | _tagN :: restNrow =>
                                                              match restNrow with
                                                              | [] => none
                                                              | N :: restDone =>
                                                                  match restDone with
                                                                  | [] =>
                                                                      some
                                                                        (PrefixTreeUp.mk
                                                                          (prefixTreeDecodeBHist V)
                                                                          (prefixTreeDecodeBHist E)
                                                                          (prefixTreeDecodeBHist F)
                                                                          (prefixTreeDecodeBHist W)
                                                                          (prefixTreeDecodeBHist H)
                                                                          (prefixTreeDecodeBHist C)
                                                                          (prefixTreeDecodeBHist P)
                                                                          (prefixTreeDecodeBHist N))
                                                                  | _ :: _ => none

private theorem prefixTree_round_trip :
    ∀ x : PrefixTreeUp,
      prefixTreeFromEventFlow (prefixTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V E F W H C P N =>
      change
        some
          (PrefixTreeUp.mk
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist V))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist E))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist F))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist W))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist H))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist C))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist P))
            (prefixTreeDecodeBHist (prefixTreeEncodeBHist N))) =
          some (PrefixTreeUp.mk V E F W H C P N)
      rw [prefixTree_decode_encode_bhist V, prefixTree_decode_encode_bhist E,
        prefixTree_decode_encode_bhist F, prefixTree_decode_encode_bhist W,
        prefixTree_decode_encode_bhist H, prefixTree_decode_encode_bhist C,
        prefixTree_decode_encode_bhist P, prefixTree_decode_encode_bhist N]

private theorem prefixTreeToEventFlow_injective
    {x y : PrefixTreeUp} :
    prefixTreeToEventFlow x = prefixTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      prefixTreeFromEventFlow (prefixTreeToEventFlow x) =
        prefixTreeFromEventFlow (prefixTreeToEventFlow y) :=
    congrArg prefixTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (prefixTree_round_trip x).symm
      (Eq.trans hread (prefixTree_round_trip y)))

instance prefixTreeBHistCarrier : BHistCarrier PrefixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := prefixTreeToEventFlow
  fromEventFlow := prefixTreeFromEventFlow

instance prefixTreeChapterTasteGate : ChapterTasteGate PrefixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change prefixTreeFromEventFlow (prefixTreeToEventFlow x) = some x
    exact prefixTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (prefixTreeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrefixTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  prefixTreeChapterTasteGate

theorem PrefixTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, prefixTreeDecodeBHist (prefixTreeEncodeBHist h) = h) ∧
      (∀ x : PrefixTreeUp, prefixTreeFromEventFlow (prefixTreeToEventFlow x) = some x) ∧
        prefixTreeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk V E F W H C P N =>
          exact
            congrArg some
              (prefixTree_mk_congr
                (prefixTree_decode_encode_bhist V)
                (prefixTree_decode_encode_bhist E)
                (prefixTree_decode_encode_bhist F)
                (prefixTree_decode_encode_bhist W)
                (prefixTree_decode_encode_bhist H)
                (prefixTree_decode_encode_bhist C)
                (prefixTree_decode_encode_bhist P)
                (prefixTree_decode_encode_bhist N))
    · rfl

end BEDC.Derived.PrefixTreeUp
