import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicsFalsificationSurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicsFalsificationSurfaceUp : Type where
  | mk (R L E K B A G H C Q N : BHist) : PhysicsFalsificationSurfaceUp
  deriving DecidableEq

def physicsFalsificationSurfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicsFalsificationSurfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicsFalsificationSurfaceEncodeBHist h

def physicsFalsificationSurfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicsFalsificationSurfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicsFalsificationSurfaceDecodeBHist tail)

private def physicsFalsificationSurfaceNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => physicsFalsificationSurfaceNthRawEvent tail n

private theorem physicsFalsificationSurface_decode_encode_bhist :
    ∀ h : BHist,
      physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem physicsFalsificationSurface_mk_congr
    {R R' L L' E E' K K' B B' A A' G G' H H' C C' Q Q' N N' : BHist}
    (hR : R' = R)
    (hL : L' = L)
    (hE : E' = E)
    (hK : K' = K)
    (hB : B' = B)
    (hA : A' = A)
    (hG : G' = G)
    (hH : H' = H)
    (hC : C' = C)
    (hQ : Q' = Q)
    (hN : N' = N) :
    PhysicsFalsificationSurfaceUp.mk R' L' E' K' B' A' G' H' C' Q' N' =
      PhysicsFalsificationSurfaceUp.mk R L E K B A G H C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hL
  cases hE
  cases hK
  cases hB
  cases hA
  cases hG
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def physicsFalsificationSurfaceFields :
    PhysicsFalsificationSurfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsFalsificationSurfaceUp.mk R L E K B A G H C Q N =>
      [R, L, E, K, B, A, G, H, C, Q, N]

def physicsFalsificationSurfaceToEventFlow :
    PhysicsFalsificationSurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsFalsificationSurfaceUp.mk R L E K B A G H C Q N =>
      [physicsFalsificationSurfaceEncodeBHist R,
        physicsFalsificationSurfaceEncodeBHist L,
        physicsFalsificationSurfaceEncodeBHist E,
        physicsFalsificationSurfaceEncodeBHist K,
        physicsFalsificationSurfaceEncodeBHist B,
        physicsFalsificationSurfaceEncodeBHist A,
        physicsFalsificationSurfaceEncodeBHist G,
        physicsFalsificationSurfaceEncodeBHist H,
        physicsFalsificationSurfaceEncodeBHist C,
        physicsFalsificationSurfaceEncodeBHist Q,
        physicsFalsificationSurfaceEncodeBHist N]

def physicsFalsificationSurfaceFromEventFlow
    (ef : EventFlow) : Option PhysicsFalsificationSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhysicsFalsificationSurfaceUp.mk
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 0))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 1))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 2))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 3))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 4))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 5))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 6))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 7))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 8))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 9))
      (physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceNthRawEvent ef 10)))

private theorem physicsFalsificationSurface_round_trip :
    ∀ x : PhysicsFalsificationSurfaceUp,
      physicsFalsificationSurfaceFromEventFlow
        (physicsFalsificationSurfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R L E K B A G H C Q N =>
      exact
        congrArg some
          (physicsFalsificationSurface_mk_congr
            (physicsFalsificationSurface_decode_encode_bhist R)
            (physicsFalsificationSurface_decode_encode_bhist L)
            (physicsFalsificationSurface_decode_encode_bhist E)
            (physicsFalsificationSurface_decode_encode_bhist K)
            (physicsFalsificationSurface_decode_encode_bhist B)
            (physicsFalsificationSurface_decode_encode_bhist A)
            (physicsFalsificationSurface_decode_encode_bhist G)
            (physicsFalsificationSurface_decode_encode_bhist H)
            (physicsFalsificationSurface_decode_encode_bhist C)
            (physicsFalsificationSurface_decode_encode_bhist Q)
            (physicsFalsificationSurface_decode_encode_bhist N))

private theorem physicsFalsificationSurfaceToEventFlow_injective
    {x y : PhysicsFalsificationSurfaceUp} :
    physicsFalsificationSurfaceToEventFlow x =
      physicsFalsificationSurfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicsFalsificationSurfaceFromEventFlow
          (physicsFalsificationSurfaceToEventFlow x) =
        physicsFalsificationSurfaceFromEventFlow
          (physicsFalsificationSurfaceToEventFlow y) :=
    congrArg physicsFalsificationSurfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicsFalsificationSurface_round_trip x).symm
      (Eq.trans hread (physicsFalsificationSurface_round_trip y)))

private theorem physicsFalsificationSurface_field_faithful :
    ∀ x y : PhysicsFalsificationSurfaceUp,
      physicsFalsificationSurfaceFields x = physicsFalsificationSurfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R L E K B A G H C Q N =>
      cases y with
      | mk R' L' E' K' B' A' G' H' C' Q' N' =>
          cases hfields
          rfl

instance physicsFalsificationSurfaceBHistCarrier :
    BHistCarrier PhysicsFalsificationSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicsFalsificationSurfaceToEventFlow
  fromEventFlow := physicsFalsificationSurfaceFromEventFlow

instance physicsFalsificationSurfaceChapterTasteGate :
    ChapterTasteGate PhysicsFalsificationSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicsFalsificationSurfaceFromEventFlow
        (physicsFalsificationSurfaceToEventFlow x) = some x
    exact physicsFalsificationSurface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicsFalsificationSurfaceToEventFlow_injective heq)

instance physicsFalsificationSurfaceFieldFaithful :
    FieldFaithful PhysicsFalsificationSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicsFalsificationSurfaceFields
  field_faithful := physicsFalsificationSurface_field_faithful

instance physicsFalsificationSurfaceNontrivial :
    Nontrivial PhysicsFalsificationSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicsFalsificationSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhysicsFalsificationSurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicsFalsificationSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicsFalsificationSurfaceChapterTasteGate

theorem PhysicsFalsificationSurfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      physicsFalsificationSurfaceDecodeBHist
        (physicsFalsificationSurfaceEncodeBHist h) = h) ∧
      (∀ x : PhysicsFalsificationSurfaceUp,
        physicsFalsificationSurfaceFromEventFlow
          (physicsFalsificationSurfaceToEventFlow x) = some x) ∧
        (∀ x y : PhysicsFalsificationSurfaceUp,
          physicsFalsificationSurfaceToEventFlow x =
              physicsFalsificationSurfaceToEventFlow y →
            x = y) ∧
          physicsFalsificationSurfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨physicsFalsificationSurface_decode_encode_bhist,
      physicsFalsificationSurface_round_trip,
      (fun _x _y heq => physicsFalsificationSurfaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PhysicsFalsificationSurfaceUp
