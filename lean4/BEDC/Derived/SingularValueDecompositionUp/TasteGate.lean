import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SingularValueDecompositionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SingularValueDecompositionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (A U V D L R F Q T H C P N : BHist) : SingularValueDecompositionUp
  deriving DecidableEq

def SingularValueDecompositionCarrier [AskSetup] [PackageSetup]
    (A U V D L R F Q T H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory A ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
    UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory F ∧ UnaryHistory Q ∧
      UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem SingularValueDecompositionFiniteMatrixHandoff [AskSetup] [PackageSetup]
    {A U V D L R F Q T H C P N matrixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SingularValueDecompositionCarrier A U V D L R F Q T H C P N bundle pkg →
      Cont A L matrixRead →
        PkgSig bundle matrixRead pkg →
          UnaryHistory A ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
            UnaryHistory L ∧ UnaryHistory matrixRead ∧ Cont A L matrixRead ∧
              PkgSig bundle N pkg ∧ PkgSig bundle matrixRead pkg := by
  -- BEDC touchpoint anchor: SingularValueDecompositionCarrier BHist Cont PkgSig UnaryHistory
  intro carrier matrixRoute matrixPkg
  obtain ⟨aUnary, uUnary, vUnary, dUnary, lUnary, _rUnary, _fUnary, _qUnary,
    _tUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, namePkg⟩ := carrier
  have matrixUnary : UnaryHistory matrixRead :=
    unary_cont_closed aUnary lUnary matrixRoute
  exact
    ⟨aUnary, uUnary, vUnary, dUnary, lUnary, matrixUnary, matrixRoute, namePkg,
      matrixPkg⟩

def SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist h

def SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SingularValueDecompositionTasteGate_single_carrier_alignment_fields :
    SingularValueDecompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SingularValueDecompositionUp.mk A U V D L R F Q T H C P N =>
      [A, U, V, D, L, R, F, Q, T, H, C, P, N]

def SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow :
    SingularValueDecompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (SingularValueDecompositionTasteGate_single_carrier_alignment_fields x).map
        SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist

private def SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt index rest

def SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option SingularValueDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SingularValueDecompositionUp.mk
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 9 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 10 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 11 ef))
      (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
        (SingularValueDecompositionTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem SingularValueDecompositionTasteGate_single_carrier_alignment_round_trip
    (x : SingularValueDecompositionUp) :
    SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow
      (SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A U V D L R F Q T H C P N =>
      change
        some
          (SingularValueDecompositionUp.mk
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist A))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist U))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist V))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist D))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist L))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist R))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist F))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist Q))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist T))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist H))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist C))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist P))
            (SingularValueDecompositionTasteGate_single_carrier_alignment_decodeBHist
              (SingularValueDecompositionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SingularValueDecompositionUp.mk A U V D L R F Q T H C P N)
      rw [SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode A,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode U,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode V,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode D,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode L,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode R,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode F,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode Q,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode T,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode H,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode C,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode P,
        SingularValueDecompositionTasteGate_single_carrier_alignment_decode_encode N]

private theorem SingularValueDecompositionTasteGate_single_carrier_alignment_injective
    {x y : SingularValueDecompositionUp} :
    SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow x =
      SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow
          (SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow x) =
        SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow
          (SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SingularValueDecompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SingularValueDecompositionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SingularValueDecompositionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : SingularValueDecompositionUp,
      SingularValueDecompositionTasteGate_single_carrier_alignment_fields x =
        SingularValueDecompositionTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 U1 V1 D1 L1 R1 F1 Q1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 U2 V2 D2 L2 R2 F2 Q2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance singularValueDecompositionBHistCarrier :
    BHistCarrier SingularValueDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow

instance singularValueDecompositionChapterTasteGate :
    ChapterTasteGate SingularValueDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SingularValueDecompositionTasteGate_single_carrier_alignment_fromEventFlow
        (SingularValueDecompositionTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact SingularValueDecompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SingularValueDecompositionTasteGate_single_carrier_alignment_injective heq)

instance singularValueDecompositionFieldFaithful :
    FieldFaithful SingularValueDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SingularValueDecompositionTasteGate_single_carrier_alignment_fields
  field_faithful := SingularValueDecompositionTasteGate_single_carrier_alignment_field_faithful

theorem SingularValueDecompositionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SingularValueDecompositionUp) ∧
      Nonempty (FieldFaithful SingularValueDecompositionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨⟨singularValueDecompositionChapterTasteGate⟩, ⟨singularValueDecompositionFieldFaithful⟩⟩

end BEDC.Derived.SingularValueDecompositionUp
