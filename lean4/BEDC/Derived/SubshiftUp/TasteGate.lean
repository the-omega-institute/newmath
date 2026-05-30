import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubshiftUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubshiftUp : Type where
  | mk (A W L S C B H K P N : BHist) : SubshiftUp
  deriving DecidableEq

def subshiftEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subshiftEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subshiftEncodeBHist h

def subshiftDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subshiftDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subshiftDecodeBHist tail)

private theorem subshift_decode_encode_bhist :
    ∀ h : BHist, subshiftDecodeBHist (subshiftEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subshiftFields : SubshiftUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubshiftUp.mk A W L S C B H K P N => [A, W, L, S, C, B, H, K, P, N]

def subshiftToEventFlow : SubshiftUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (subshiftFields x).map subshiftEncodeBHist

private def subshiftEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subshiftEventAtDefault index rest

def subshiftFromEventFlow (ef : EventFlow) : Option SubshiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubshiftUp.mk
      (subshiftDecodeBHist (subshiftEventAtDefault 0 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 1 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 2 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 3 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 4 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 5 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 6 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 7 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 8 ef))
      (subshiftDecodeBHist (subshiftEventAtDefault 9 ef)))

private theorem subshift_mk_congr
    {A A' W W' L L' S S' C C' B B' H H' K K' P P' N N' : BHist}
    (hA : A' = A) (hW : W' = W) (hL : L' = L) (hS : S' = S)
    (hC : C' = C) (hB : B' = B) (hH : H' = H) (hK : K' = K)
    (hP : P' = P) (hN : N' = N) :
    SubshiftUp.mk A' W' L' S' C' B' H' K' P' N' =
      SubshiftUp.mk A W L S C B H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hW
  cases hL
  cases hS
  cases hC
  cases hB
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

private theorem subshiftEncodeBHist_injective {h k : BHist} :
    subshiftEncodeBHist h = subshiftEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      subshiftDecodeBHist (subshiftEncodeBHist h) =
        subshiftDecodeBHist (subshiftEncodeBHist k) :=
    congrArg subshiftDecodeBHist heq
  exact Eq.trans (subshift_decode_encode_bhist h).symm
    (Eq.trans hdecode (subshift_decode_encode_bhist k))

private theorem subshift_round_trip :
    ∀ x : SubshiftUp, subshiftFromEventFlow (subshiftToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W L S C B H K P N =>
      change
        some
          (SubshiftUp.mk
            (subshiftDecodeBHist (subshiftEncodeBHist A))
            (subshiftDecodeBHist (subshiftEncodeBHist W))
            (subshiftDecodeBHist (subshiftEncodeBHist L))
            (subshiftDecodeBHist (subshiftEncodeBHist S))
            (subshiftDecodeBHist (subshiftEncodeBHist C))
            (subshiftDecodeBHist (subshiftEncodeBHist B))
            (subshiftDecodeBHist (subshiftEncodeBHist H))
            (subshiftDecodeBHist (subshiftEncodeBHist K))
            (subshiftDecodeBHist (subshiftEncodeBHist P))
            (subshiftDecodeBHist (subshiftEncodeBHist N))) =
          some (SubshiftUp.mk A W L S C B H K P N)
      exact congrArg some
        (subshift_mk_congr
          (subshift_decode_encode_bhist A)
          (subshift_decode_encode_bhist W)
          (subshift_decode_encode_bhist L)
          (subshift_decode_encode_bhist S)
          (subshift_decode_encode_bhist C)
          (subshift_decode_encode_bhist B)
          (subshift_decode_encode_bhist H)
          (subshift_decode_encode_bhist K)
          (subshift_decode_encode_bhist P)
          (subshift_decode_encode_bhist N))

private theorem subshiftToEventFlow_injective {x y : SubshiftUp} :
    subshiftToEventFlow x = subshiftToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk A₁ W₁ L₁ S₁ C₁ B₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk A₂ W₂ L₂ S₂ C₂ B₂ H₂ K₂ P₂ N₂ =>
          change
            [subshiftEncodeBHist A₁, subshiftEncodeBHist W₁, subshiftEncodeBHist L₁,
              subshiftEncodeBHist S₁, subshiftEncodeBHist C₁, subshiftEncodeBHist B₁,
              subshiftEncodeBHist H₁, subshiftEncodeBHist K₁, subshiftEncodeBHist P₁,
              subshiftEncodeBHist N₁] =
            [subshiftEncodeBHist A₂, subshiftEncodeBHist W₂, subshiftEncodeBHist L₂,
              subshiftEncodeBHist S₂, subshiftEncodeBHist C₂, subshiftEncodeBHist B₂,
              subshiftEncodeBHist H₂, subshiftEncodeBHist K₂, subshiftEncodeBHist P₂,
              subshiftEncodeBHist N₂] at heq
          injection heq with hA tailA
          injection tailA with hW tailW
          injection tailW with hL tailL
          injection tailL with hS tailS
          injection tailS with hC tailC
          injection tailC with hB tailB
          injection tailB with hH tailH
          injection tailH with hK tailK
          injection tailK with hP tailP
          injection tailP with hN _
          exact
            subshift_mk_congr
              (subshiftEncodeBHist_injective hA)
              (subshiftEncodeBHist_injective hW)
              (subshiftEncodeBHist_injective hL)
              (subshiftEncodeBHist_injective hS)
              (subshiftEncodeBHist_injective hC)
              (subshiftEncodeBHist_injective hB)
              (subshiftEncodeBHist_injective hH)
              (subshiftEncodeBHist_injective hK)
              (subshiftEncodeBHist_injective hP)
              (subshiftEncodeBHist_injective hN)

private theorem subshift_field_faithful :
    ∀ x y : SubshiftUp, subshiftFields x = subshiftFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ W₁ L₁ S₁ C₁ B₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk A₂ W₂ L₂ S₂ C₂ B₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance subshiftBHistCarrier : BHistCarrier SubshiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subshiftToEventFlow
  fromEventFlow := subshiftFromEventFlow

instance subshiftChapterTasteGate : ChapterTasteGate SubshiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subshiftFromEventFlow (subshiftToEventFlow x) = some x
    exact subshift_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subshiftToEventFlow_injective heq)

instance subshiftFieldFaithful : FieldFaithful SubshiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subshiftFields
  field_faithful := subshift_field_faithful

instance subshiftNontrivial : Nontrivial SubshiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubshiftUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubshiftUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubshiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subshiftChapterTasteGate

theorem SubshiftTasteGate_single_carrier_alignment :
    (∀ h : BHist, subshiftDecodeBHist (subshiftEncodeBHist h) = h) ∧
      (∀ x : SubshiftUp, subshiftFromEventFlow (subshiftToEventFlow x) = some x) ∧
        (∀ x y : SubshiftUp,
          subshiftToEventFlow x = subshiftToEventFlow y → x = y) ∧
          subshiftEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨subshift_decode_encode_bhist,
      subshift_round_trip,
      (fun _ _ heq => subshiftToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SubshiftUp
