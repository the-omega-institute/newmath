import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCeilingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCeilingUp : Type where
  | mk : (x k c p l u M R E H T P N : BHist) → DyadicCeilingUp
  deriving DecidableEq

def dyadicCeilingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCeilingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCeilingEncodeBHist h

def dyadicCeilingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCeilingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCeilingDecodeBHist tail)

private theorem dyadicCeiling_decode_encode_bhist :
    ∀ h : BHist, dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCeilingFields : DyadicCeilingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCeilingUp.mk x k c p l u M R E H T P N => [x, k, c, p, l, u, M, R, E, H, T, P, N]

def dyadicCeilingToEventFlow : DyadicCeilingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | z => (dyadicCeilingFields z).map dyadicCeilingEncodeBHist

def dyadicCeilingFromEventFlow : EventFlow → Option DyadicCeilingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | x :: rest0 =>
      match rest0 with
      | [] => none
      | k :: rest1 =>
          match rest1 with
          | [] => none
          | c :: rest2 =>
              match rest2 with
              | [] => none
              | p :: rest3 =>
                  match rest3 with
                  | [] => none
                  | l :: rest4 =>
                      match rest4 with
                      | [] => none
                      | u :: rest5 =>
                          match rest5 with
                          | [] => none
                          | M :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | T :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (DyadicCeilingUp.mk
                                                              (dyadicCeilingDecodeBHist x)
                                                              (dyadicCeilingDecodeBHist k)
                                                              (dyadicCeilingDecodeBHist c)
                                                              (dyadicCeilingDecodeBHist p)
                                                              (dyadicCeilingDecodeBHist l)
                                                              (dyadicCeilingDecodeBHist u)
                                                              (dyadicCeilingDecodeBHist M)
                                                              (dyadicCeilingDecodeBHist R)
                                                              (dyadicCeilingDecodeBHist E)
                                                              (dyadicCeilingDecodeBHist H)
                                                              (dyadicCeilingDecodeBHist T)
                                                              (dyadicCeilingDecodeBHist P)
                                                              (dyadicCeilingDecodeBHist N))
                                                      | _ :: _ => none

private theorem dyadicCeiling_round_trip :
    ∀ z : DyadicCeilingUp,
      dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow z) = some z := by
  -- BEDC touchpoint anchor: BHist BMark
  intro z
  cases z with
  | mk x k c p l u M R E H T P N =>
      change
        some
            (DyadicCeilingUp.mk
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist x))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist k))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist c))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist p))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist l))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist u))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist M))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist R))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist E))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist H))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist T))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist P))
              (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist N))) =
          some (DyadicCeilingUp.mk x k c p l u M R E H T P N)
      rw [dyadicCeiling_decode_encode_bhist x,
        dyadicCeiling_decode_encode_bhist k,
        dyadicCeiling_decode_encode_bhist c,
        dyadicCeiling_decode_encode_bhist p,
        dyadicCeiling_decode_encode_bhist l,
        dyadicCeiling_decode_encode_bhist u,
        dyadicCeiling_decode_encode_bhist M,
        dyadicCeiling_decode_encode_bhist R,
        dyadicCeiling_decode_encode_bhist E,
        dyadicCeiling_decode_encode_bhist H,
        dyadicCeiling_decode_encode_bhist T,
        dyadicCeiling_decode_encode_bhist P,
        dyadicCeiling_decode_encode_bhist N]

private theorem dyadicCeilingToEventFlow_injective {x y : DyadicCeilingUp} :
    dyadicCeilingToEventFlow x = dyadicCeilingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) =
        dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow y) :=
    congrArg dyadicCeilingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicCeiling_round_trip x).symm
      (Eq.trans hread (dyadicCeiling_round_trip y)))

instance dyadicCeilingBHistCarrier : BHistCarrier DyadicCeilingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCeilingToEventFlow
  fromEventFlow := dyadicCeilingFromEventFlow

instance dyadicCeilingChapterTasteGate : ChapterTasteGate DyadicCeilingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro z
    change dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow z) = some z
    exact dyadicCeiling_round_trip z
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicCeilingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicCeilingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCeilingChapterTasteGate

theorem DyadicCeilingTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist h) = h) ∧
      (∀ x : DyadicCeilingUp,
        dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) = some x) ∧
        (∀ x y : DyadicCeilingUp,
          dyadicCeilingToEventFlow x = dyadicCeilingToEventFlow y → x = y) ∧
          dyadicCeilingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨dyadicCeiling_decode_encode_bhist,
      dyadicCeiling_round_trip,
      (fun _ _ heq => dyadicCeilingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicCeilingUp
