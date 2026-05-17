import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceSocketUp : Type where
  | mk : (T K U A S R H C P N : BHist) → MachineInterfaceSocketUp

def machineInterfaceSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceSocketEncodeBHist h

def machineInterfaceSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceSocketDecodeBHist tail)

private theorem machineInterfaceSocketDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem machineInterfaceSocket_mk_congr
    {T T' K K' U U' A A' S S' R R' H H' C C' P P' N N' : BHist}
    (hT : T' = T) (hK : K' = K) (hU : U' = U) (hA : A' = A)
    (hS : S' = S) (hR : R' = R) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    MachineInterfaceSocketUp.mk T' K' U' A' S' R' H' C' P' N' =
      MachineInterfaceSocketUp.mk T K U A S R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hK
  cases hU
  cases hA
  cases hS
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def machineInterfaceSocketFields : MachineInterfaceSocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceSocketUp.mk T K U A S R H C P N => [T, K, U, A, S, R, H, C, P, N]

def machineInterfaceSocketToEventFlow : MachineInterfaceSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (machineInterfaceSocketFields x).map machineInterfaceSocketEncodeBHist

def machineInterfaceSocketFromEventFlow : EventFlow → Option MachineInterfaceSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _T :: [] => none
  | _T :: _K :: [] => none
  | _T :: _K :: _U :: [] => none
  | _T :: _K :: _U :: _A :: [] => none
  | _T :: _K :: _U :: _A :: _S :: [] => none
  | _T :: _K :: _U :: _A :: _S :: _R :: [] => none
  | _T :: _K :: _U :: _A :: _S :: _R :: _H :: [] => none
  | _T :: _K :: _U :: _A :: _S :: _R :: _H :: _C :: [] => none
  | _T :: _K :: _U :: _A :: _S :: _R :: _H :: _C :: _P :: [] => none
  | T :: K :: U :: A :: S :: R :: H :: C :: P :: N :: [] =>
      some
        (MachineInterfaceSocketUp.mk
          (machineInterfaceSocketDecodeBHist T)
          (machineInterfaceSocketDecodeBHist K)
          (machineInterfaceSocketDecodeBHist U)
          (machineInterfaceSocketDecodeBHist A)
          (machineInterfaceSocketDecodeBHist S)
          (machineInterfaceSocketDecodeBHist R)
          (machineInterfaceSocketDecodeBHist H)
          (machineInterfaceSocketDecodeBHist C)
          (machineInterfaceSocketDecodeBHist P)
          (machineInterfaceSocketDecodeBHist N))
  | _T :: _K :: _U :: _A :: _S :: _R :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem machineInterfaceSocket_round_trip :
    ∀ x : MachineInterfaceSocketUp,
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T K U A S R H C P N =>
      exact
        congrArg some
          (machineInterfaceSocket_mk_congr
            (machineInterfaceSocketDecode_encode_bhist T)
            (machineInterfaceSocketDecode_encode_bhist K)
            (machineInterfaceSocketDecode_encode_bhist U)
            (machineInterfaceSocketDecode_encode_bhist A)
            (machineInterfaceSocketDecode_encode_bhist S)
            (machineInterfaceSocketDecode_encode_bhist R)
            (machineInterfaceSocketDecode_encode_bhist H)
            (machineInterfaceSocketDecode_encode_bhist C)
            (machineInterfaceSocketDecode_encode_bhist P)
            (machineInterfaceSocketDecode_encode_bhist N))

private theorem machineInterfaceSocketToEventFlow_injective
    {x y : MachineInterfaceSocketUp} :
    machineInterfaceSocketToEventFlow x = machineInterfaceSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) =
        machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow y) :=
    congrArg machineInterfaceSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineInterfaceSocket_round_trip x).symm
      (Eq.trans hread (machineInterfaceSocket_round_trip y)))

private theorem machineInterfaceSocket_field_faithful :
    ∀ x y : MachineInterfaceSocketUp, machineInterfaceSocketFields x =
      machineInterfaceSocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T K U A S R H C P N =>
      cases y with
      | mk T' K' U' A' S' R' H' C' P' N' =>
          cases hfields
          rfl

instance machineInterfaceSocketBHistCarrier : BHistCarrier MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceSocketToEventFlow
  fromEventFlow := machineInterfaceSocketFromEventFlow

instance machineInterfaceSocketChapterTasteGate : ChapterTasteGate MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x
    exact machineInterfaceSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceSocketToEventFlow_injective heq)

instance machineInterfaceSocketFieldFaithful : FieldFaithful MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineInterfaceSocketFields
  field_faithful := machineInterfaceSocket_field_faithful

instance machineInterfaceSocketNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceSocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MachineInterfaceSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceSocketChapterTasteGate

theorem MachineInterfaceSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist, machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist h) = h) ∧
      (∀ x : MachineInterfaceSocketUp,
        machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x) ∧
        (∀ x y : MachineInterfaceSocketUp,
          machineInterfaceSocketToEventFlow x = machineInterfaceSocketToEventFlow y → x = y) ∧
          machineInterfaceSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact machineInterfaceSocketDecode_encode_bhist
  · constructor
    · exact machineInterfaceSocket_round_trip
    · constructor
      · intro x y heq
        exact machineInterfaceSocketToEventFlow_injective heq
      · rfl

end BEDC.Derived.MachineInterfaceSocketUp
