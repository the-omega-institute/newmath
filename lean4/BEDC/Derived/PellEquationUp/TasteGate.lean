import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PellEquationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PellEquationUp : Type where
  | mk (D X Y N Q V L H C K M : BHist) : PellEquationUp
  deriving DecidableEq

def PellEquationTasteGate_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: PellEquationTasteGate_encodeBHist h
  | BHist.e1 h => BMark.b1 :: PellEquationTasteGate_encodeBHist h

def PellEquationTasteGate_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (PellEquationTasteGate_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (PellEquationTasteGate_decodeBHist tail)

private theorem PellEquationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PellEquationTasteGate_fields : PellEquationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PellEquationUp.mk D X Y N Q V L H C K M => [D, X, Y, N, Q, V, L, H, C, K, M]

def PellEquationTasteGate_toEventFlow : PellEquationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (PellEquationTasteGate_fields x).map PellEquationTasteGate_encodeBHist

private def PellEquationTasteGate_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => PellEquationTasteGate_eventAt index rest

def PellEquationTasteGate_fromEventFlow (flow : EventFlow) : Option PellEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PellEquationUp.mk
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 0 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 1 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 2 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 3 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 4 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 5 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 6 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 7 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 8 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 9 flow))
      (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_eventAt 10 flow)))

private theorem PellEquationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PellEquationUp,
      PellEquationTasteGate_fromEventFlow (PellEquationTasteGate_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D X Y N Q V L H C K M =>
      change
        some
          (PellEquationUp.mk
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist D))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist X))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist Y))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist N))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist Q))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist V))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist L))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist H))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist C))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist K))
            (PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist M))) =
          some (PellEquationUp.mk D X Y N Q V L H C K M)
      rw [PellEquationTasteGate_single_carrier_alignment_decode D,
        PellEquationTasteGate_single_carrier_alignment_decode X,
        PellEquationTasteGate_single_carrier_alignment_decode Y,
        PellEquationTasteGate_single_carrier_alignment_decode N,
        PellEquationTasteGate_single_carrier_alignment_decode Q,
        PellEquationTasteGate_single_carrier_alignment_decode V,
        PellEquationTasteGate_single_carrier_alignment_decode L,
        PellEquationTasteGate_single_carrier_alignment_decode H,
        PellEquationTasteGate_single_carrier_alignment_decode C,
        PellEquationTasteGate_single_carrier_alignment_decode K,
        PellEquationTasteGate_single_carrier_alignment_decode M]

private theorem PellEquationTasteGate_toEventFlow_injective {x y : PellEquationUp} :
    PellEquationTasteGate_toEventFlow x = PellEquationTasteGate_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PellEquationTasteGate_fromEventFlow (PellEquationTasteGate_toEventFlow x) =
        PellEquationTasteGate_fromEventFlow (PellEquationTasteGate_toEventFlow y) :=
    congrArg PellEquationTasteGate_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PellEquationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PellEquationTasteGate_single_carrier_alignment_round_trip y)))

private theorem PellEquationTasteGate_field_faithful :
    ∀ x y : PellEquationUp,
      PellEquationTasteGate_fields x = PellEquationTasteGate_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 X1 Y1 N1 Q1 V1 L1 H1 C1 K1 M1 =>
      cases y with
      | mk D2 X2 Y2 N2 Q2 V2 L2 H2 C2 K2 M2 =>
          cases hfields
          rfl

instance pellEquationBHistCarrier : BHistCarrier PellEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PellEquationTasteGate_toEventFlow
  fromEventFlow := PellEquationTasteGate_fromEventFlow

instance pellEquationChapterTasteGate : ChapterTasteGate PellEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change PellEquationTasteGate_fromEventFlow (PellEquationTasteGate_toEventFlow x) = some x
    exact PellEquationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PellEquationTasteGate_toEventFlow_injective heq)

instance pellEquationFieldFaithful : FieldFaithful PellEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := PellEquationTasteGate_fields
  field_faithful := PellEquationTasteGate_field_faithful

instance pellEquationNontrivial : Nontrivial PellEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PellEquationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PellEquationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PellEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pellEquationChapterTasteGate

def taste_gate_witness : FieldFaithful PellEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pellEquationFieldFaithful

theorem PellEquationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      PellEquationTasteGate_decodeBHist (PellEquationTasteGate_encodeBHist h) = h) ∧
      PellEquationTasteGate_fields
        (PellEquationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨PellEquationTasteGate_single_carrier_alignment_decode, rfl⟩

def PellEquationCarrier [AskSetup] [PackageSetup]
    (D X Y N Q V L H C K M : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory N ∧
    UnaryHistory Q ∧ UnaryHistory V ∧ UnaryHistory L ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory M ∧
        PkgSig bundle K pkg ∧ PkgSig bundle M pkg

theorem PellEquation_norm_preservation [AskSetup] [PackageSetup]
    {D X Y N Q V L H C K M normRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PellEquationCarrier D X Y N Q V L H C K M bundle pkg ->
      Cont D X normRead ->
        Cont normRead Y witnessRead ->
          PkgSig bundle witnessRead pkg ->
            UnaryHistory N ∧ UnaryHistory normRead ∧ UnaryHistory witnessRead ∧
              Cont D X normRead ∧ Cont normRead Y witnessRead ∧
                PkgSig bundle K pkg ∧ PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier normRoute witnessRoute witnessPkg
  obtain ⟨dUnary, xUnary, yUnary, nUnary, _qUnary, _vUnary, _lUnary, _hUnary, _cUnary,
    _kUnary, _mUnary, provenancePkg, _localNamePkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed dUnary xUnary normRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed normUnary yUnary witnessRoute
  exact
    ⟨nUnary, normUnary, witnessUnary, normRoute, witnessRoute, provenancePkg, witnessPkg⟩

end BEDC.Derived.PellEquationUp
