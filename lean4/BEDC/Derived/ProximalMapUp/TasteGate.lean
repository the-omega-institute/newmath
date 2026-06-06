import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProximalMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProximalMapUp : Type where
  | mk (X F u z R D K G O H C P N : BHist) : ProximalMapUp
  deriving DecidableEq

def proximalMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proximalMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proximalMapEncodeBHist h

def proximalMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proximalMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proximalMapDecodeBHist tail)

private theorem ProximalMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, proximalMapDecodeBHist (proximalMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def proximalMapFields : ProximalMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProximalMapUp.mk X F u z R D K G O H C P N => [X, F, u, z, R, D, K, G, O, H, C, P, N]

def proximalMapToEventFlow : ProximalMapUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (proximalMapFields x).map proximalMapEncodeBHist

private def proximalMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proximalMapEventAtDefault index rest

def proximalMapFromEventFlow (ef : EventFlow) : Option ProximalMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProximalMapUp.mk
      (proximalMapDecodeBHist (proximalMapEventAtDefault 0 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 1 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 2 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 3 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 4 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 5 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 6 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 7 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 8 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 9 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 10 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 11 ef))
      (proximalMapDecodeBHist (proximalMapEventAtDefault 12 ef)))

private theorem ProximalMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProximalMapUp,
      proximalMapFromEventFlow (proximalMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F u z R D K G O H C P N =>
      change
        some
          (ProximalMapUp.mk
            (proximalMapDecodeBHist (proximalMapEncodeBHist X))
            (proximalMapDecodeBHist (proximalMapEncodeBHist F))
            (proximalMapDecodeBHist (proximalMapEncodeBHist u))
            (proximalMapDecodeBHist (proximalMapEncodeBHist z))
            (proximalMapDecodeBHist (proximalMapEncodeBHist R))
            (proximalMapDecodeBHist (proximalMapEncodeBHist D))
            (proximalMapDecodeBHist (proximalMapEncodeBHist K))
            (proximalMapDecodeBHist (proximalMapEncodeBHist G))
            (proximalMapDecodeBHist (proximalMapEncodeBHist O))
            (proximalMapDecodeBHist (proximalMapEncodeBHist H))
            (proximalMapDecodeBHist (proximalMapEncodeBHist C))
            (proximalMapDecodeBHist (proximalMapEncodeBHist P))
            (proximalMapDecodeBHist (proximalMapEncodeBHist N))) =
          some (ProximalMapUp.mk X F u z R D K G O H C P N)
      rw [ProximalMapTasteGate_single_carrier_alignment_decode X,
        ProximalMapTasteGate_single_carrier_alignment_decode F,
        ProximalMapTasteGate_single_carrier_alignment_decode u,
        ProximalMapTasteGate_single_carrier_alignment_decode z,
        ProximalMapTasteGate_single_carrier_alignment_decode R,
        ProximalMapTasteGate_single_carrier_alignment_decode D,
        ProximalMapTasteGate_single_carrier_alignment_decode K,
        ProximalMapTasteGate_single_carrier_alignment_decode G,
        ProximalMapTasteGate_single_carrier_alignment_decode O,
        ProximalMapTasteGate_single_carrier_alignment_decode H,
        ProximalMapTasteGate_single_carrier_alignment_decode C,
        ProximalMapTasteGate_single_carrier_alignment_decode P,
        ProximalMapTasteGate_single_carrier_alignment_decode N]

private theorem ProximalMapTasteGate_single_carrier_alignment_injective
    {x y : ProximalMapUp} :
    proximalMapToEventFlow x = proximalMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proximalMapFromEventFlow (proximalMapToEventFlow x) =
        proximalMapFromEventFlow (proximalMapToEventFlow y) :=
    congrArg proximalMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProximalMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProximalMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProximalMapTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProximalMapUp, proximalMapFields x = proximalMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ F₁ u₁ z₁ R₁ D₁ K₁ G₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ F₂ u₂ z₂ R₂ D₂ K₂ G₂ O₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hF tail1
          injection tail1 with hu tail2
          injection tail2 with hz tail3
          injection tail3 with hR tail4
          injection tail4 with hD tail5
          injection tail5 with hK tail6
          injection tail6 with hG tail7
          injection tail7 with hO tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst hX
          subst hF
          subst hu
          subst hz
          subst hR
          subst hD
          subst hK
          subst hG
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance proximalMapBHistCarrier : BHistCarrier ProximalMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proximalMapToEventFlow
  fromEventFlow := proximalMapFromEventFlow

instance proximalMapChapterTasteGate : ChapterTasteGate ProximalMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proximalMapFromEventFlow (proximalMapToEventFlow x) = some x
    exact ProximalMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProximalMapTasteGate_single_carrier_alignment_injective heq)

instance proximalMapFieldFaithful : FieldFaithful ProximalMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proximalMapFields
  field_faithful := ProximalMapTasteGate_single_carrier_alignment_fields

instance proximalMapNontrivial : Nontrivial ProximalMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProximalMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ProximalMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProximalMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proximalMapChapterTasteGate

theorem ProximalMapTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ProximalMapUp) ∧ Nonempty (ChapterTasteGate ProximalMapUp) ∧
      Nonempty (FieldFaithful ProximalMapUp) ∧ Nonempty (Nontrivial ProximalMapUp) ∧
        (∀ X F u z R D K G O H C P N : BHist,
          proximalMapFields (ProximalMapUp.mk X F u z R D K G O H C P N) =
            [X, F, u, z, R, D, K, G, O, H, C, P, N]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨proximalMapBHistCarrier⟩, ⟨proximalMapChapterTasteGate⟩,
      ⟨proximalMapFieldFaithful⟩, ⟨proximalMapNontrivial⟩, by
        intro X F u z R D K G O H C P N
        rfl⟩

end BEDC.Derived.ProximalMapUp
