import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MengerCoverCompactnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MengerCoverCompactnessUp : Type where
  | mk (K R B W Q E H C P N : BHist) : MengerCoverCompactnessUp
  deriving DecidableEq

def mengerCoverCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mengerCoverCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mengerCoverCompactnessEncodeBHist h

def mengerCoverCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mengerCoverCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mengerCoverCompactnessDecodeBHist tail)

private theorem mengerCoverCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mengerCoverCompactnessFields : MengerCoverCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MengerCoverCompactnessUp.mk K R B W Q E H C P N => [K, R, B, W, Q, E, H, C, P, N]

def mengerCoverCompactnessToEventFlow : MengerCoverCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map mengerCoverCompactnessEncodeBHist (mengerCoverCompactnessFields x)

private def mengerCoverCompactnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mengerCoverCompactnessEventAtDefault index rest

def mengerCoverCompactnessFromEventFlow (ef : EventFlow) : Option MengerCoverCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MengerCoverCompactnessUp.mk
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 0 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 1 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 2 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 3 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 4 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 5 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 6 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 7 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 8 ef))
      (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEventAtDefault 9 ef)))

private theorem mengerCoverCompactness_round_trip :
    ∀ x : MengerCoverCompactnessUp,
      mengerCoverCompactnessFromEventFlow (mengerCoverCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K R B W Q E H C P N =>
      change
        some
          (MengerCoverCompactnessUp.mk
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist K))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist R))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist B))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist W))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist Q))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist E))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist H))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist C))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist P))
            (mengerCoverCompactnessDecodeBHist (mengerCoverCompactnessEncodeBHist N))) =
          some (MengerCoverCompactnessUp.mk K R B W Q E H C P N)
      rw [mengerCoverCompactnessDecode_encode_bhist K,
        mengerCoverCompactnessDecode_encode_bhist R,
        mengerCoverCompactnessDecode_encode_bhist B,
        mengerCoverCompactnessDecode_encode_bhist W,
        mengerCoverCompactnessDecode_encode_bhist Q,
        mengerCoverCompactnessDecode_encode_bhist E,
        mengerCoverCompactnessDecode_encode_bhist H,
        mengerCoverCompactnessDecode_encode_bhist C,
        mengerCoverCompactnessDecode_encode_bhist P,
        mengerCoverCompactnessDecode_encode_bhist N]

private theorem mengerCoverCompactnessToEventFlow_injective
    {x y : MengerCoverCompactnessUp} :
    mengerCoverCompactnessToEventFlow x = mengerCoverCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mengerCoverCompactnessFromEventFlow (mengerCoverCompactnessToEventFlow x) =
        mengerCoverCompactnessFromEventFlow (mengerCoverCompactnessToEventFlow y) :=
    congrArg mengerCoverCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mengerCoverCompactness_round_trip x).symm
      (Eq.trans hread (mengerCoverCompactness_round_trip y)))

private theorem mengerCoverCompactness_field_faithful :
    ∀ x y : MengerCoverCompactnessUp,
      mengerCoverCompactnessFields x = mengerCoverCompactnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ R₁ B₁ W₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ R₂ B₂ W₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tK
          injection tK with hR tR
          injection tR with hB tB
          injection tB with hW tW
          injection tW with hQ tQ
          injection tQ with hE tE
          injection tE with hH tH
          injection tH with hC tC
          injection tC with hP tP
          injection tP with hN _
          subst hK
          subst hR
          subst hB
          subst hW
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance mengerCoverCompactnessBHistCarrier : BHistCarrier MengerCoverCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mengerCoverCompactnessToEventFlow
  fromEventFlow := mengerCoverCompactnessFromEventFlow

instance mengerCoverCompactnessChapterTasteGate :
    ChapterTasteGate MengerCoverCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mengerCoverCompactnessFromEventFlow (mengerCoverCompactnessToEventFlow x) = some x
    exact mengerCoverCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mengerCoverCompactnessToEventFlow_injective heq)

instance mengerCoverCompactnessFieldFaithful :
    FieldFaithful MengerCoverCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mengerCoverCompactnessFields
  field_faithful := mengerCoverCompactness_field_faithful

instance mengerCoverCompactnessNontrivial : Nontrivial MengerCoverCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MengerCoverCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MengerCoverCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MengerCoverCompactnessCarrier_namecert_obligations
    (x : MengerCoverCompactnessUp) :
    ∃ K R B W Q E H C P N : BHist,
      x = MengerCoverCompactnessUp.mk K R B W Q E H C P N ∧
        FieldFaithful.fields x = [K, R, B, W, Q, E, H, C, P, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            Cont C P (append C P) ∧ hsame (append C P) (append C P) := by
  -- BEDC touchpoint anchor: BHist hsame Cont FieldFaithful BHistCarrier
  cases x with
  | mk K R B W Q E H C P N =>
      exact
        ⟨K, R, B, W, Q, E, H, C, P, N, rfl, rfl,
          mengerCoverCompactness_round_trip
            (MengerCoverCompactnessUp.mk K R B W Q E H C P N),
          rfl, hsame_refl (append C P)⟩

end BEDC.Derived.MengerCoverCompactnessUp
