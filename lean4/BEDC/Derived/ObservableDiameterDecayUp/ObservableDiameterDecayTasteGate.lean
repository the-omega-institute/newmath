import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservableDiameterDecayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservableDiameterDecayUp : Type where
  | mk (K F L T M H C P N : BHist) : ObservableDiameterDecayUp
  deriving DecidableEq

def observableDiameterDecayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observableDiameterDecayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observableDiameterDecayEncodeBHist h

def observableDiameterDecayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observableDiameterDecayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observableDiameterDecayDecodeBHist tail)

private def observableDiameterDecayRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => observableDiameterDecayRawAt n rest

private theorem observableDiameterDecay_decode_encode_bhist :
    ∀ h : BHist, observableDiameterDecayDecodeBHist (observableDiameterDecayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observableDiameterDecay_mk_congr
    {K K' F F' L L' T T' M M' H H' C C' P P' N N' : BHist}
    (hK : K' = K)
    (hF : F' = F)
    (hL : L' = L)
    (hT : T' = T)
    (hM : M' = M)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    ObservableDiameterDecayUp.mk K' F' L' T' M' H' C' P' N' =
      ObservableDiameterDecayUp.mk K F L T M H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hF
  cases hL
  cases hT
  cases hM
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def observableDiameterDecayFields : ObservableDiameterDecayUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservableDiameterDecayUp.mk K F L T M H C P N => [K, F, L, T, M, H, C, P, N]

def observableDiameterDecayToEventFlow : ObservableDiameterDecayUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservableDiameterDecayUp.mk K F L T M H C P N =>
      [observableDiameterDecayEncodeBHist K,
        observableDiameterDecayEncodeBHist F,
        observableDiameterDecayEncodeBHist L,
        observableDiameterDecayEncodeBHist T,
        observableDiameterDecayEncodeBHist M,
        observableDiameterDecayEncodeBHist H,
        observableDiameterDecayEncodeBHist C,
        observableDiameterDecayEncodeBHist P,
        observableDiameterDecayEncodeBHist N]

def observableDiameterDecayFromEventFlow (ef : EventFlow) : Option ObservableDiameterDecayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ObservableDiameterDecayUp.mk
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 0 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 1 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 2 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 3 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 4 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 5 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 6 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 7 ef))
      (observableDiameterDecayDecodeBHist (observableDiameterDecayRawAt 8 ef)))

private theorem observableDiameterDecay_round_trip :
    ∀ x : ObservableDiameterDecayUp,
      observableDiameterDecayFromEventFlow (observableDiameterDecayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F L T M H C P N =>
      exact
        congrArg some
          (observableDiameterDecay_mk_congr
            (observableDiameterDecay_decode_encode_bhist K)
            (observableDiameterDecay_decode_encode_bhist F)
            (observableDiameterDecay_decode_encode_bhist L)
            (observableDiameterDecay_decode_encode_bhist T)
            (observableDiameterDecay_decode_encode_bhist M)
            (observableDiameterDecay_decode_encode_bhist H)
            (observableDiameterDecay_decode_encode_bhist C)
            (observableDiameterDecay_decode_encode_bhist P)
            (observableDiameterDecay_decode_encode_bhist N))

private theorem observableDiameterDecayToEventFlow_injective {x y : ObservableDiameterDecayUp} :
    observableDiameterDecayToEventFlow x = observableDiameterDecayToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observableDiameterDecayFromEventFlow (observableDiameterDecayToEventFlow x) =
        observableDiameterDecayFromEventFlow (observableDiameterDecayToEventFlow y) :=
    congrArg observableDiameterDecayFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observableDiameterDecay_round_trip x).symm
      (Eq.trans hread (observableDiameterDecay_round_trip y)))

private theorem observableDiameterDecay_field_faithful :
    ∀ x y : ObservableDiameterDecayUp,
      observableDiameterDecayFields x = observableDiameterDecayFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 L1 T1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 L2 T2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance observableDiameterDecayBHistCarrier : BHistCarrier ObservableDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observableDiameterDecayToEventFlow
  fromEventFlow := observableDiameterDecayFromEventFlow

instance observableDiameterDecayChapterTasteGate :
    ChapterTasteGate ObservableDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observableDiameterDecayFromEventFlow (observableDiameterDecayToEventFlow x) = some x
    exact observableDiameterDecay_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observableDiameterDecayToEventFlow_injective heq)

instance observableDiameterDecayFieldFaithful :
    FieldFaithful ObservableDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observableDiameterDecayFields
  field_faithful := observableDiameterDecay_field_faithful

instance observableDiameterDecayNontrivial :
    Nontrivial ObservableDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservableDiameterDecayUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservableDiameterDecayUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservableDiameterDecayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observableDiameterDecayChapterTasteGate

theorem ObservableDiameterDecayTasteGate_single_carrier_alignment :
    (forall h : BHist, observableDiameterDecayDecodeBHist (observableDiameterDecayEncodeBHist h) = h) /\
      (forall x : ObservableDiameterDecayUp,
        observableDiameterDecayFromEventFlow (observableDiameterDecayToEventFlow x) = some x) /\
        (forall x y : ObservableDiameterDecayUp,
          observableDiameterDecayToEventFlow x = observableDiameterDecayToEventFlow y -> x = y) /\
          observableDiameterDecayEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨observableDiameterDecay_decode_encode_bhist,
      ⟨observableDiameterDecay_round_trip,
        ⟨fun _x _y heq => observableDiameterDecayToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.ObservableDiameterDecayUp
