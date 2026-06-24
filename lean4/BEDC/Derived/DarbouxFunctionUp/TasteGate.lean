import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxFunctionUp : Type where
  | mk (I R G B C D H K P N : BHist) : DarbouxFunctionUp
  deriving DecidableEq

def darbouxFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxFunctionEncodeBHist h

def darbouxFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxFunctionDecodeBHist tail)

private theorem DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def darbouxFunctionFields : DarbouxFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxFunctionUp.mk I R G B C D H K P N =>
      [I, R, G, B, C, D, H, K, P, N]

def darbouxFunctionToEventFlow : DarbouxFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxFunctionFields x).map darbouxFunctionEncodeBHist

private def darbouxFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxFunctionEventAtDefault index rest

def darbouxFunctionFromEventFlow (ef : EventFlow) : Option DarbouxFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxFunctionUp.mk
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 0 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 1 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 2 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 3 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 4 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 5 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 6 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 7 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 8 ef))
      (darbouxFunctionDecodeBHist (darbouxFunctionEventAtDefault 9 ef)))

private theorem DarbouxFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxFunctionUp,
      darbouxFunctionFromEventFlow (darbouxFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I R G B C D H K P N =>
      change
        some
          (DarbouxFunctionUp.mk
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist I))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist R))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist G))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist B))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist C))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist D))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist H))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist K))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist P))
            (darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist N))) =
          some (DarbouxFunctionUp.mk I R G B C D H K P N)
      rw [DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode I,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode G,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode B,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode C,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode D,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode K,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DarbouxFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxFunctionUp} :
    darbouxFunctionToEventFlow x = darbouxFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxFunctionFromEventFlow (darbouxFunctionToEventFlow x) =
        darbouxFunctionFromEventFlow (darbouxFunctionToEventFlow y) :=
    congrArg darbouxFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DarbouxFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance darbouxFunctionBHistCarrier : BHistCarrier DarbouxFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxFunctionToEventFlow
  fromEventFlow := darbouxFunctionFromEventFlow

instance darbouxFunctionChapterTasteGate : ChapterTasteGate DarbouxFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxFunctionFromEventFlow (darbouxFunctionToEventFlow x) = some x
    exact DarbouxFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance darbouxFunctionFieldFaithful : FieldFaithful DarbouxFunctionUp where
  fields := darbouxFunctionFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk I₁ R₁ G₁ B₁ C₁ D₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk I₂ R₂ G₂ B₂ C₂ D₂ H₂ K₂ P₂ N₂ =>
        injection h with hI t1
        injection t1 with hR t2
        injection t2 with hG t3
        injection t3 with hB t4
        injection t4 with hC t5
        injection t5 with hD t6
        injection t6 with hH t7
        injection t7 with hK t8
        injection t8 with hP t9
        injection t9 with hN _
        subst hI
        subst hR
        subst hG
        subst hB
        subst hC
        subst hD
        subst hH
        subst hK
        subst hP
        subst hN
        rfl

instance darbouxFunctionNontrivial : Nontrivial DarbouxFunctionUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨DarbouxFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DarbouxFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hI
        cases hI⟩

def taste_gate : ChapterTasteGate DarbouxFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxFunctionChapterTasteGate

theorem DarbouxFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxFunctionDecodeBHist (darbouxFunctionEncodeBHist h) = h) ∧
      (∀ x : DarbouxFunctionUp,
        darbouxFunctionFromEventFlow (darbouxFunctionToEventFlow x) = some x) ∧
      (∀ x y : DarbouxFunctionUp,
        darbouxFunctionToEventFlow x = darbouxFunctionToEventFlow y → x = y) ∧
      darbouxFunctionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      Nonempty (ChapterTasteGate DarbouxFunctionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DarbouxFunctionTasteGate_single_carrier_alignment_decode_encode,
      ⟨DarbouxFunctionTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
            DarbouxFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq,
          ⟨rfl, ⟨darbouxFunctionChapterTasteGate⟩⟩⟩⟩⟩

end BEDC.Derived.DarbouxFunctionUp
