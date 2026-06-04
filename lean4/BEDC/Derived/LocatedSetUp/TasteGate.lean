import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSetUp : Type where
  | mk : (X A Q R E T H C P N : BHist) → LocatedSetUp
  deriving DecidableEq

def locatedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSetEncodeBHist h

def locatedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSetDecodeBHist tail)

private def locatedSetRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locatedSetRawAt n rest

private theorem locatedSet_decode_encode_bhist :
    ∀ h : BHist, locatedSetDecodeBHist (locatedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem locatedSet_mk_congr
    {X X' A A' Q Q' R R' E E' T T' H H' C C' P P' N N' : BHist}
    (hX : X' = X)
    (hA : A' = A)
    (hQ : Q' = Q)
    (hR : R' = R)
    (hE : E' = E)
    (hT : T' = T)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    LocatedSetUp.mk X' A' Q' R' E' T' H' C' P' N' =
      LocatedSetUp.mk X A Q R E T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hA
  cases hQ
  cases hR
  cases hE
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def locatedSetFields : LocatedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSetUp.mk X A Q R E T H C P N => [X, A, Q, R, E, T, H, C, P, N]

def locatedSetToEventFlow : LocatedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSetUp.mk X A Q R E T H C P N =>
      [locatedSetEncodeBHist X,
        locatedSetEncodeBHist A,
        locatedSetEncodeBHist Q,
        locatedSetEncodeBHist R,
        locatedSetEncodeBHist E,
        locatedSetEncodeBHist T,
        locatedSetEncodeBHist H,
        locatedSetEncodeBHist C,
        locatedSetEncodeBHist P,
        locatedSetEncodeBHist N]

def locatedSetFromEventFlow (ef : EventFlow) : Option LocatedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedSetUp.mk
      (locatedSetDecodeBHist (locatedSetRawAt 0 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 1 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 2 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 3 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 4 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 5 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 6 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 7 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 8 ef))
      (locatedSetDecodeBHist (locatedSetRawAt 9 ef)))

private theorem locatedSet_round_trip :
    ∀ x : LocatedSetUp, locatedSetFromEventFlow (locatedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A Q R E T H C P N =>
      exact
        congrArg some
          (locatedSet_mk_congr
            (locatedSet_decode_encode_bhist X)
            (locatedSet_decode_encode_bhist A)
            (locatedSet_decode_encode_bhist Q)
            (locatedSet_decode_encode_bhist R)
            (locatedSet_decode_encode_bhist E)
            (locatedSet_decode_encode_bhist T)
            (locatedSet_decode_encode_bhist H)
            (locatedSet_decode_encode_bhist C)
            (locatedSet_decode_encode_bhist P)
            (locatedSet_decode_encode_bhist N))

private theorem locatedSetToEventFlow_injective
    {x y : LocatedSetUp} :
    locatedSetToEventFlow x = locatedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSetFromEventFlow (locatedSetToEventFlow x) =
        locatedSetFromEventFlow (locatedSetToEventFlow y) :=
    congrArg locatedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedSet_round_trip x).symm
      (Eq.trans hread (locatedSet_round_trip y)))

private theorem locatedSet_fields_faithful :
    ∀ x y : LocatedSetUp, locatedSetFields x = locatedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ A₁ Q₁ R₁ E₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ A₂ Q₂ R₂ E₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedSetBHistCarrier : BHistCarrier LocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSetToEventFlow
  fromEventFlow := locatedSetFromEventFlow

instance locatedSetChapterTasteGate : ChapterTasteGate LocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSetFromEventFlow (locatedSetToEventFlow x) = some x
    exact locatedSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedSetToEventFlow_injective heq)

instance locatedSetFieldFaithful : FieldFaithful LocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedSetFields
  field_faithful := locatedSet_fields_faithful

instance locatedSetNontrivial : Nontrivial LocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedSetDecodeBHist (locatedSetEncodeBHist h) = h) ∧
      (∀ x : LocatedSetUp, locatedSetFromEventFlow (locatedSetToEventFlow x) = some x) ∧
        (∀ x y : LocatedSetUp,
          locatedSetToEventFlow x = locatedSetToEventFlow y → x = y) ∧
          locatedSetEncodeBHist BHist.Empty = ([] : List BMark) ∧
            Nonempty (ChapterTasteGate LocatedSetUp) ∧
              Nonempty (FieldFaithful LocatedSetUp) ∧
                Nonempty (Nontrivial LocatedSetUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨locatedSet_decode_encode_bhist,
      ⟨locatedSet_round_trip,
        ⟨fun _x _y heq => locatedSetToEventFlow_injective heq,
          ⟨rfl,
            ⟨⟨locatedSetChapterTasteGate⟩,
              ⟨⟨locatedSetFieldFaithful⟩,
                ⟨locatedSetNontrivial⟩⟩⟩⟩⟩⟩⟩

theorem LocatedSet_distance_handoff (x : LocatedSetUp) :
    ∃ X A Q R E T H C P N : BHist,
      x = LocatedSetUp.mk X A Q R E T H C P N ∧
        locatedSetFields x = [X, A, Q, R, E, T, H, C, P, N] ∧
          Cont X A (append X A) ∧
            Cont A Q (append A Q) ∧
              Cont Q R (append Q R) ∧
                Cont R E (append R E) ∧
                  Cont E T (append E T) ∧
                    hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk X A Q R E T H C P N =>
      exact
        ⟨X, A, Q, R, E, T, H, C, P, N, rfl, rfl, cont_intro rfl,
          cont_intro rfl, cont_intro rfl, cont_intro rfl, cont_intro rfl,
          hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩

end BEDC.Derived.LocatedSetUp
