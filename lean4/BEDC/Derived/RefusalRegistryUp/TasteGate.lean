import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RefusalRegistryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RefusalRegistryUp : Type where
  | mk (B E G C S V T P N : BHist) : RefusalRegistryUp
  deriving DecidableEq

def refusalRegistryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: refusalRegistryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: refusalRegistryEncodeBHist h

def refusalRegistryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (refusalRegistryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (refusalRegistryDecodeBHist tail)

private def refusalRegistryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => refusalRegistryRawAt n rest

private theorem refusalRegistry_decode_encode_bhist :
    ∀ h : BHist, refusalRegistryDecodeBHist (refusalRegistryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem refusalRegistry_mk_congr
    {B B' E E' G G' C C' S S' V V' T T' P P' N N' : BHist}
    (hB : B' = B)
    (hE : E' = E)
    (hG : G' = G)
    (hC : C' = C)
    (hS : S' = S)
    (hV : V' = V)
    (hT : T' = T)
    (hP : P' = P)
    (hN : N' = N) :
    RefusalRegistryUp.mk B' E' G' C' S' V' T' P' N' =
      RefusalRegistryUp.mk B E G C S V T P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hE
  cases hG
  cases hC
  cases hS
  cases hV
  cases hT
  cases hP
  cases hN
  rfl

def refusalRegistryFields : RefusalRegistryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RefusalRegistryUp.mk B E G C S V T P N => [B, E, G, C, S, V, T, P, N]

def refusalRegistryToEventFlow : RefusalRegistryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RefusalRegistryUp.mk B E G C S V T P N =>
      [refusalRegistryEncodeBHist B,
        refusalRegistryEncodeBHist E,
        refusalRegistryEncodeBHist G,
        refusalRegistryEncodeBHist C,
        refusalRegistryEncodeBHist S,
        refusalRegistryEncodeBHist V,
        refusalRegistryEncodeBHist T,
        refusalRegistryEncodeBHist P,
        refusalRegistryEncodeBHist N]

def refusalRegistryFromEventFlow (ef : EventFlow) : Option RefusalRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RefusalRegistryUp.mk
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 0 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 1 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 2 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 3 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 4 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 5 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 6 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 7 ef))
      (refusalRegistryDecodeBHist (refusalRegistryRawAt 8 ef)))

private theorem refusalRegistry_round_trip :
    ∀ x : RefusalRegistryUp,
      refusalRegistryFromEventFlow (refusalRegistryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E G C S V T P N =>
      exact
        congrArg some
          (refusalRegistry_mk_congr
            (refusalRegistry_decode_encode_bhist B)
            (refusalRegistry_decode_encode_bhist E)
            (refusalRegistry_decode_encode_bhist G)
            (refusalRegistry_decode_encode_bhist C)
            (refusalRegistry_decode_encode_bhist S)
            (refusalRegistry_decode_encode_bhist V)
            (refusalRegistry_decode_encode_bhist T)
            (refusalRegistry_decode_encode_bhist P)
            (refusalRegistry_decode_encode_bhist N))

private theorem refusalRegistryToEventFlow_injective {x y : RefusalRegistryUp} :
    refusalRegistryToEventFlow x = refusalRegistryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      refusalRegistryFromEventFlow (refusalRegistryToEventFlow x) =
        refusalRegistryFromEventFlow (refusalRegistryToEventFlow y) :=
    congrArg refusalRegistryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (refusalRegistry_round_trip x).symm
      (Eq.trans hread (refusalRegistry_round_trip y)))

private theorem refusalRegistry_field_faithful :
    ∀ x y : RefusalRegistryUp,
      refusalRegistryFields x = refusalRegistryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 E1 G1 C1 S1 V1 T1 P1 N1 =>
      cases y with
      | mk B2 E2 G2 C2 S2 V2 T2 P2 N2 =>
          cases hfields
          rfl

instance refusalRegistryBHistCarrier : BHistCarrier RefusalRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := refusalRegistryToEventFlow
  fromEventFlow := refusalRegistryFromEventFlow

instance refusalRegistryChapterTasteGate :
    ChapterTasteGate RefusalRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change refusalRegistryFromEventFlow (refusalRegistryToEventFlow x) = some x
    exact refusalRegistry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (refusalRegistryToEventFlow_injective heq)

instance refusalRegistryFieldFaithful :
    FieldFaithful RefusalRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := refusalRegistryFields
  field_faithful := refusalRegistry_field_faithful

instance refusalRegistryNontrivial :
    Nontrivial RefusalRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RefusalRegistryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RefusalRegistryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RefusalRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  refusalRegistryChapterTasteGate

theorem RefusalRegistryTasteGate_single_carrier_alignment :
    (forall h : BHist, refusalRegistryDecodeBHist (refusalRegistryEncodeBHist h) = h) /\
      (forall x : RefusalRegistryUp,
        refusalRegistryFromEventFlow (refusalRegistryToEventFlow x) = some x) /\
        (forall x y : RefusalRegistryUp,
          refusalRegistryToEventFlow x = refusalRegistryToEventFlow y -> x = y) /\
          refusalRegistryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨refusalRegistry_decode_encode_bhist,
      ⟨refusalRegistry_round_trip,
        ⟨fun _x _y heq => refusalRegistryToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.RefusalRegistryUp
