import BEDC.Derived.EudoxusRealUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EudoxusRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def eudoxusRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eudoxusRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eudoxusRealEncodeBHist h

def eudoxusRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eudoxusRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eudoxusRealDecodeBHist tail)

private theorem eudoxusReal_decode_encode_bhist :
    ∀ h : BHist, eudoxusRealDecodeBHist (eudoxusRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eudoxusRealFields : EudoxusRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EudoxusRealUp.mk I A B D S Q R H C P N => [I, A, B, D, S, Q, R, H, C, P, N]

def eudoxusRealToEventFlow : EudoxusRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eudoxusRealFields x).map eudoxusRealEncodeBHist

private def eudoxusRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eudoxusRealEventAtDefault index rest

def eudoxusRealFromEventFlow (ef : EventFlow) : Option EudoxusRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EudoxusRealUp.mk
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 0 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 1 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 2 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 3 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 4 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 5 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 6 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 7 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 8 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 9 ef))
      (eudoxusRealDecodeBHist (eudoxusRealEventAtDefault 10 ef)))

private theorem eudoxusReal_mk_congr
    {I I' A A' B B' D D' S S' Q Q' R R' H H' C C' P P' N N' : BHist}
    (hI : I' = I) (hA : A' = A) (hB : B' = B) (hD : D' = D)
    (hS : S' = S) (hQ : Q' = Q) (hR : R' = R) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    EudoxusRealUp.mk I' A' B' D' S' Q' R' H' C' P' N' =
      EudoxusRealUp.mk I A B D S Q R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hA
  cases hB
  cases hD
  cases hS
  cases hQ
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem eudoxusRealEncodeBHist_injective {h k : BHist} :
    eudoxusRealEncodeBHist h = eudoxusRealEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      eudoxusRealDecodeBHist (eudoxusRealEncodeBHist h) =
        eudoxusRealDecodeBHist (eudoxusRealEncodeBHist k) :=
    congrArg eudoxusRealDecodeBHist heq
  exact Eq.trans (eudoxusReal_decode_encode_bhist h).symm
    (Eq.trans hdecode (eudoxusReal_decode_encode_bhist k))

private theorem eudoxusReal_round_trip :
    ∀ x : EudoxusRealUp,
      eudoxusRealFromEventFlow (eudoxusRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I A B D S Q R H C P N =>
      change
        some
          (EudoxusRealUp.mk
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist I))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist A))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist B))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist D))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist S))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist Q))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist R))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist H))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist C))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist P))
            (eudoxusRealDecodeBHist (eudoxusRealEncodeBHist N))) =
          some (EudoxusRealUp.mk I A B D S Q R H C P N)
      exact congrArg some
        (eudoxusReal_mk_congr
          (eudoxusReal_decode_encode_bhist I)
          (eudoxusReal_decode_encode_bhist A)
          (eudoxusReal_decode_encode_bhist B)
          (eudoxusReal_decode_encode_bhist D)
          (eudoxusReal_decode_encode_bhist S)
          (eudoxusReal_decode_encode_bhist Q)
          (eudoxusReal_decode_encode_bhist R)
          (eudoxusReal_decode_encode_bhist H)
          (eudoxusReal_decode_encode_bhist C)
          (eudoxusReal_decode_encode_bhist P)
          (eudoxusReal_decode_encode_bhist N))

private theorem eudoxusRealToEventFlow_injective {x y : EudoxusRealUp} :
    eudoxusRealToEventFlow x = eudoxusRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk I₁ A₁ B₁ D₁ S₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ A₂ B₂ D₂ S₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          change
            [eudoxusRealEncodeBHist I₁, eudoxusRealEncodeBHist A₁,
              eudoxusRealEncodeBHist B₁, eudoxusRealEncodeBHist D₁,
              eudoxusRealEncodeBHist S₁, eudoxusRealEncodeBHist Q₁,
              eudoxusRealEncodeBHist R₁, eudoxusRealEncodeBHist H₁,
              eudoxusRealEncodeBHist C₁, eudoxusRealEncodeBHist P₁,
              eudoxusRealEncodeBHist N₁] =
            [eudoxusRealEncodeBHist I₂, eudoxusRealEncodeBHist A₂,
              eudoxusRealEncodeBHist B₂, eudoxusRealEncodeBHist D₂,
              eudoxusRealEncodeBHist S₂, eudoxusRealEncodeBHist Q₂,
              eudoxusRealEncodeBHist R₂, eudoxusRealEncodeBHist H₂,
              eudoxusRealEncodeBHist C₂, eudoxusRealEncodeBHist P₂,
              eudoxusRealEncodeBHist N₂] at heq
          injection heq with hI tailI
          injection tailI with hA tailA
          injection tailA with hB tailB
          injection tailB with hD tailD
          injection tailD with hS tailS
          injection tailS with hQ tailQ
          injection tailQ with hR tailR
          injection tailR with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          exact
            eudoxusReal_mk_congr
              (eudoxusRealEncodeBHist_injective hI)
              (eudoxusRealEncodeBHist_injective hA)
              (eudoxusRealEncodeBHist_injective hB)
              (eudoxusRealEncodeBHist_injective hD)
              (eudoxusRealEncodeBHist_injective hS)
              (eudoxusRealEncodeBHist_injective hQ)
              (eudoxusRealEncodeBHist_injective hR)
              (eudoxusRealEncodeBHist_injective hH)
              (eudoxusRealEncodeBHist_injective hC)
              (eudoxusRealEncodeBHist_injective hP)
              (eudoxusRealEncodeBHist_injective hN)

private theorem eudoxusReal_field_faithful :
    ∀ x y : EudoxusRealUp, eudoxusRealFields x = eudoxusRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ A₁ B₁ D₁ S₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ A₂ B₂ D₂ S₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance eudoxusRealBHistCarrier : BHistCarrier EudoxusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eudoxusRealToEventFlow
  fromEventFlow := eudoxusRealFromEventFlow

instance eudoxusRealChapterTasteGate : ChapterTasteGate EudoxusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eudoxusRealFromEventFlow (eudoxusRealToEventFlow x) = some x
    exact eudoxusReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (eudoxusRealToEventFlow_injective heq)

instance eudoxusRealFieldFaithful : FieldFaithful EudoxusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eudoxusRealFields
  field_faithful := eudoxusReal_field_faithful

instance eudoxusRealNontrivial : Nontrivial EudoxusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EudoxusRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EudoxusRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EudoxusRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eudoxusRealChapterTasteGate

theorem EudoxusRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, eudoxusRealDecodeBHist (eudoxusRealEncodeBHist h) = h) ∧
      (∀ x : EudoxusRealUp,
        eudoxusRealFromEventFlow (eudoxusRealToEventFlow x) = some x) ∧
        (∀ x y : EudoxusRealUp,
          eudoxusRealToEventFlow x = eudoxusRealToEventFlow y → x = y) ∧
          eudoxusRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨eudoxusReal_decode_encode_bhist,
      eudoxusReal_round_trip,
      (fun _ _ heq => eudoxusRealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EudoxusRealUp
