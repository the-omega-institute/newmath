import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrecompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrecompactMetricUp : Type where
  | mk (X D N F R M H C G Q : BHist) : PrecompactMetricUp
  deriving DecidableEq

def precompactMetricFields : PrecompactMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrecompactMetricUp.mk X D N F R M H C G Q => [X, D, N, F, R, M, H, C, G, Q]

def precompactMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: precompactMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: precompactMetricEncodeBHist h

def precompactMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (precompactMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (precompactMetricDecodeBHist tail)

private theorem PrecompactMetricTasteGate_single_carrier_alignment_decode :
    forall h : BHist, precompactMetricDecodeBHist (precompactMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def precompactMetricToEventFlow : PrecompactMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (precompactMetricFields x).map precompactMetricEncodeBHist

private def precompactMetricRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => precompactMetricRawAt n rest

def precompactMetricFromEventFlow (flow : EventFlow) : Option PrecompactMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PrecompactMetricUp.mk
      (precompactMetricDecodeBHist (precompactMetricRawAt 0 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 1 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 2 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 3 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 4 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 5 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 6 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 7 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 8 flow))
      (precompactMetricDecodeBHist (precompactMetricRawAt 9 flow)))

private theorem PrecompactMetricTasteGate_single_carrier_alignment_round_trip
    (x : PrecompactMetricUp) :
    precompactMetricFromEventFlow (precompactMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X D N F R M H C G Q =>
      change
        some
          (PrecompactMetricUp.mk
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist X))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist D))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist N))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist F))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist R))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist M))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist H))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist C))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist G))
            (precompactMetricDecodeBHist (precompactMetricEncodeBHist Q))) =
          some (PrecompactMetricUp.mk X D N F R M H C G Q)
      rw [PrecompactMetricTasteGate_single_carrier_alignment_decode X,
        PrecompactMetricTasteGate_single_carrier_alignment_decode D,
        PrecompactMetricTasteGate_single_carrier_alignment_decode N,
        PrecompactMetricTasteGate_single_carrier_alignment_decode F,
        PrecompactMetricTasteGate_single_carrier_alignment_decode R,
        PrecompactMetricTasteGate_single_carrier_alignment_decode M,
        PrecompactMetricTasteGate_single_carrier_alignment_decode H,
        PrecompactMetricTasteGate_single_carrier_alignment_decode C,
        PrecompactMetricTasteGate_single_carrier_alignment_decode G,
        PrecompactMetricTasteGate_single_carrier_alignment_decode Q]

private theorem PrecompactMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PrecompactMetricUp} :
    precompactMetricToEventFlow x = precompactMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      precompactMetricFromEventFlow (precompactMetricToEventFlow x) =
        precompactMetricFromEventFlow (precompactMetricToEventFlow y) :=
    congrArg precompactMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PrecompactMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PrecompactMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem PrecompactMetricTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : PrecompactMetricUp, precompactMetricFields x = precompactMetricFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Xa Da Na Fa Ra Ma Ha Ca Ga Qa =>
      cases y with
      | mk Xb Db Nb Fb Rb Mb Hb Cb Gb Qb =>
          cases hfields
          rfl

instance precompactMetricBHistCarrier : BHistCarrier PrecompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := precompactMetricToEventFlow
  fromEventFlow := precompactMetricFromEventFlow

instance precompactMetricChapterTasteGate : ChapterTasteGate PrecompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change precompactMetricFromEventFlow (precompactMetricToEventFlow x) = some x
    exact PrecompactMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PrecompactMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance precompactMetricFieldFaithful : FieldFaithful PrecompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := precompactMetricFields
  field_faithful := PrecompactMetricTasteGate_single_carrier_alignment_fields_faithful

instance precompactMetricNontrivial : Nontrivial PrecompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrecompactMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrecompactMetricUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem PrecompactMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PrecompactMetricUp) ∧
      Nonempty (FieldFaithful PrecompactMetricUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PrecompactMetricUp) ∧
      (∀ h : BHist, precompactMetricDecodeBHist (precompactMetricEncodeBHist h) = h) ∧
      (∀ x : PrecompactMetricUp,
        precompactMetricFromEventFlow (precompactMetricToEventFlow x) = some x) ∧
      (∀ x y : PrecompactMetricUp,
        precompactMetricToEventFlow x = precompactMetricToEventFlow y -> x = y) ∧
      precompactMetricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨precompactMetricChapterTasteGate⟩, ⟨precompactMetricFieldFaithful⟩,
      ⟨precompactMetricNontrivial⟩,
      PrecompactMetricTasteGate_single_carrier_alignment_decode,
      PrecompactMetricTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => PrecompactMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

private theorem PrecompactMetricNameCert_obligations_encode_display
    (h : BHist) :
    ∀ m, List.Mem m (precompactMetricEncodeBHist h) ->
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      intro m hm
      cases hm
  | e0 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inl rfl
      | tail _ hmTail =>
          exact ih m hmTail
  | e1 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inr rfl
      | tail _ hmTail =>
          exact ih m hmTail

private theorem PrecompactMetricNameCert_obligations_flow_display
    (rows : List BHist) :
    ∀ w m, List.Mem w (rows.map precompactMetricEncodeBHist) -> List.Mem m w ->
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction rows with
  | nil =>
      intro w m hw _hm
      cases hw
  | cons h rows ih =>
      intro w m hw hm
      cases hw with
      | head =>
          exact PrecompactMetricNameCert_obligations_encode_display h m hm
      | tail _ hwTail =>
          exact ih w m hwTail hm

theorem PrecompactMetricNameCert_obligations (x : PrecompactMetricUp) :
    (∃ rows : List BHist, rows = precompactMetricFields x) ∧
      (∀ w m, List.Mem w (precompactMetricToEventFlow x) -> List.Mem m w ->
        m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨precompactMetricFields x, rfl⟩
  · intro w m hw hm
    exact PrecompactMetricNameCert_obligations_flow_display
      (precompactMetricFields x) w m hw hm

end BEDC.Derived.PrecompactMetricUp
