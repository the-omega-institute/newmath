import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TruthResidueLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TruthResidueLedgerUp : Type where
  | mk : (O I B P F G H C Q N : BHist) → TruthResidueLedgerUp
  deriving DecidableEq

def truthResidueLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: truthResidueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: truthResidueLedgerEncodeBHist h

def truthResidueLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (truthResidueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (truthResidueLedgerDecodeBHist tail)

private def truthResidueLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => truthResidueLedgerRawAt n rest

private theorem truthResidueLedger_decode_encode_bhist :
    ∀ h : BHist, truthResidueLedgerDecodeBHist (truthResidueLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem truthResidueLedger_mk_congr
    {O O' I I' B B' P P' F F' G G' H H' C C' Q Q' N N' : BHist}
    (hO : O' = O)
    (hI : I' = I)
    (hB : B' = B)
    (hP : P' = P)
    (hF : F' = F)
    (hG : G' = G)
    (hH : H' = H)
    (hC : C' = C)
    (hQ : Q' = Q)
    (hN : N' = N) :
    TruthResidueLedgerUp.mk O' I' B' P' F' G' H' C' Q' N' =
      TruthResidueLedgerUp.mk O I B P F G H C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hO
  cases hI
  cases hB
  cases hP
  cases hF
  cases hG
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def truthResidueLedgerFields : TruthResidueLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TruthResidueLedgerUp.mk O I B P F G H C Q N =>
      [O, I, B, P, F, G, H, C, Q, N]

def truthResidueLedgerToEventFlow : TruthResidueLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TruthResidueLedgerUp.mk O I B P F G H C Q N =>
      [truthResidueLedgerEncodeBHist O,
        truthResidueLedgerEncodeBHist I,
        truthResidueLedgerEncodeBHist B,
        truthResidueLedgerEncodeBHist P,
        truthResidueLedgerEncodeBHist F,
        truthResidueLedgerEncodeBHist G,
        truthResidueLedgerEncodeBHist H,
        truthResidueLedgerEncodeBHist C,
        truthResidueLedgerEncodeBHist Q,
        truthResidueLedgerEncodeBHist N]

def truthResidueLedgerFromEventFlow (ef : EventFlow) : Option TruthResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TruthResidueLedgerUp.mk
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 0 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 1 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 2 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 3 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 4 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 5 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 6 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 7 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 8 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 9 ef)))

private theorem truthResidueLedger_round_trip :
    ∀ x : TruthResidueLedgerUp,
      truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O I B P F G H C Q N =>
      exact
        congrArg some
          (truthResidueLedger_mk_congr
            (truthResidueLedger_decode_encode_bhist O)
            (truthResidueLedger_decode_encode_bhist I)
            (truthResidueLedger_decode_encode_bhist B)
            (truthResidueLedger_decode_encode_bhist P)
            (truthResidueLedger_decode_encode_bhist F)
            (truthResidueLedger_decode_encode_bhist G)
            (truthResidueLedger_decode_encode_bhist H)
            (truthResidueLedger_decode_encode_bhist C)
            (truthResidueLedger_decode_encode_bhist Q)
            (truthResidueLedger_decode_encode_bhist N))

private theorem truthResidueLedgerToEventFlow_injective
    {x y : TruthResidueLedgerUp} :
    truthResidueLedgerToEventFlow x = truthResidueLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) =
        truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow y) :=
    congrArg truthResidueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (truthResidueLedger_round_trip x).symm
      (Eq.trans hread (truthResidueLedger_round_trip y)))

private theorem truthResidueLedger_fields_faithful :
    ∀ x y : TruthResidueLedgerUp,
      truthResidueLedgerFields x = truthResidueLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ I₁ B₁ P₁ F₁ G₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk O₂ I₂ B₂ P₂ F₂ G₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance truthResidueLedgerBHistCarrier : BHistCarrier TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := truthResidueLedgerToEventFlow
  fromEventFlow := truthResidueLedgerFromEventFlow

instance truthResidueLedgerChapterTasteGate :
    ChapterTasteGate TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x
    exact truthResidueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (truthResidueLedgerToEventFlow_injective heq)

instance truthResidueLedgerFieldFaithful :
    FieldFaithful TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := truthResidueLedgerFields
  field_faithful := truthResidueLedger_fields_faithful

instance truthResidueLedgerNontrivial :
    Nontrivial TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TruthResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TruthResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TruthResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  truthResidueLedgerChapterTasteGate

theorem TruthResidueLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, truthResidueLedgerDecodeBHist (truthResidueLedgerEncodeBHist h) = h) ∧
      (∀ x : TruthResidueLedgerUp,
        truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x) ∧
        (∀ x y : TruthResidueLedgerUp,
          truthResidueLedgerToEventFlow x = truthResidueLedgerToEventFlow y → x = y) ∧
          truthResidueLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            Nonempty (ChapterTasteGate TruthResidueLedgerUp) ∧
              Nonempty (FieldFaithful TruthResidueLedgerUp) ∧
                Nonempty (Nontrivial TruthResidueLedgerUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨truthResidueLedger_decode_encode_bhist,
      ⟨truthResidueLedger_round_trip,
        ⟨fun _x _y heq => truthResidueLedgerToEventFlow_injective heq,
          ⟨rfl,
            ⟨⟨truthResidueLedgerChapterTasteGate⟩,
              ⟨⟨truthResidueLedgerFieldFaithful⟩,
                ⟨truthResidueLedgerNontrivial⟩⟩⟩⟩⟩⟩⟩

end BEDC.Derived.TruthResidueLedgerUp
