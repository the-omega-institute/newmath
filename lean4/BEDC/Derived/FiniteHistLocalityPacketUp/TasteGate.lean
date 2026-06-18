import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteHistLocalityPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteHistLocalityPacketUp : Type where
  | mk :
      (H0 H1 L I S T C Q N : BHist) →
      FiniteHistLocalityPacketUp
  deriving DecidableEq

def finiteHistLocalityPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteHistLocalityPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteHistLocalityPacketEncodeBHist h

def finiteHistLocalityPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteHistLocalityPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteHistLocalityPacketDecodeBHist tail)

private theorem finiteHistLocalityPacket_decode_encode_bhist :
    ∀ h : BHist,
      finiteHistLocalityPacketDecodeBHist (finiteHistLocalityPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteHistLocalityPacketFields : FiniteHistLocalityPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N =>
      [H0, H1, L, I, S, T, C, Q, N]

def finiteHistLocalityPacketToEventFlow : FiniteHistLocalityPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        finiteHistLocalityPacketEncodeBHist H0,
        finiteHistLocalityPacketEncodeBHist H1,
        finiteHistLocalityPacketEncodeBHist L,
        finiteHistLocalityPacketEncodeBHist I,
        finiteHistLocalityPacketEncodeBHist S,
        finiteHistLocalityPacketEncodeBHist T,
        finiteHistLocalityPacketEncodeBHist C,
        finiteHistLocalityPacketEncodeBHist Q,
        finiteHistLocalityPacketEncodeBHist N]

def finiteHistLocalityPacketFromEventFlow :
    EventFlow → Option FiniteHistLocalityPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b0, BMark.b1], H0, H1, L, I, S, T, C, Q, N] =>
      some
        (FiniteHistLocalityPacketUp.mk
          (finiteHistLocalityPacketDecodeBHist H0)
          (finiteHistLocalityPacketDecodeBHist H1)
          (finiteHistLocalityPacketDecodeBHist L)
          (finiteHistLocalityPacketDecodeBHist I)
          (finiteHistLocalityPacketDecodeBHist S)
          (finiteHistLocalityPacketDecodeBHist T)
          (finiteHistLocalityPacketDecodeBHist C)
          (finiteHistLocalityPacketDecodeBHist Q)
          (finiteHistLocalityPacketDecodeBHist N))
  | _ => none

private theorem finiteHistLocalityPacket_round_trip :
    ∀ x : FiniteHistLocalityPacketUp,
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H0 H1 L I S T C Q N =>
      change
        some
          (FiniteHistLocalityPacketUp.mk
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist H0))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist H1))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist L))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist I))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist S))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist T))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist C))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist Q))
            (finiteHistLocalityPacketDecodeBHist
              (finiteHistLocalityPacketEncodeBHist N))) =
          some (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N)
      rw [finiteHistLocalityPacket_decode_encode_bhist H0,
        finiteHistLocalityPacket_decode_encode_bhist H1,
        finiteHistLocalityPacket_decode_encode_bhist L,
        finiteHistLocalityPacket_decode_encode_bhist I,
        finiteHistLocalityPacket_decode_encode_bhist S,
        finiteHistLocalityPacket_decode_encode_bhist T,
        finiteHistLocalityPacket_decode_encode_bhist C,
        finiteHistLocalityPacket_decode_encode_bhist Q,
        finiteHistLocalityPacket_decode_encode_bhist N]

private theorem finiteHistLocalityPacketToEventFlow_injective
    {x y : FiniteHistLocalityPacketUp} :
    finiteHistLocalityPacketToEventFlow x = finiteHistLocalityPacketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow y) :=
    congrArg finiteHistLocalityPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteHistLocalityPacket_round_trip x).symm
      (Eq.trans hread (finiteHistLocalityPacket_round_trip y)))

private theorem finiteHistLocalityPacket_field_faithful :
    ∀ x y : FiniteHistLocalityPacketUp,
      finiteHistLocalityPacketFields x = finiteHistLocalityPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H0a H1a La Ia Sa Ta Ca Qa Na =>
      cases y with
      | mk H0b H1b Lb Ib Sb Tb Cb Qb Nb =>
          injection hfields with hH0 t1
          injection t1 with hH1 t2
          injection t2 with hL t3
          injection t3 with hI t4
          injection t4 with hS t5
          injection t5 with hT t6
          injection t6 with hC t7
          injection t7 with hQ t8
          injection t8 with hN _
          cases hH0
          cases hH1
          cases hL
          cases hI
          cases hS
          cases hT
          cases hC
          cases hQ
          cases hN
          rfl

instance finiteHistLocalityPacketBHistCarrier :
    BHistCarrier FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteHistLocalityPacketToEventFlow
  fromEventFlow := finiteHistLocalityPacketFromEventFlow

instance finiteHistLocalityPacketChapterTasteGate :
    ChapterTasteGate FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteHistLocalityPacketFromEventFlow (finiteHistLocalityPacketToEventFlow x) =
        some x
    exact finiteHistLocalityPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteHistLocalityPacketToEventFlow_injective heq)

instance finiteHistLocalityPacketFieldFaithful :
    FieldFaithful FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteHistLocalityPacketFields
  field_faithful := finiteHistLocalityPacket_field_faithful

instance finiteHistLocalityPacketNontrivial :
    Nontrivial FiniteHistLocalityPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteHistLocalityPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteHistLocalityPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteHistLocalityPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteHistLocalityPacketChapterTasteGate

theorem FiniteHistLocalityPacketTasteGate_single_carrier_alignment :
    forall H0 H1 L I S T C Q N : BHist,
      finiteHistLocalityPacketToEventFlow
          (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
        [[BMark.b1, BMark.b0, BMark.b1],
          finiteHistLocalityPacketEncodeBHist H0,
          finiteHistLocalityPacketEncodeBHist H1,
          finiteHistLocalityPacketEncodeBHist L,
          finiteHistLocalityPacketEncodeBHist I,
          finiteHistLocalityPacketEncodeBHist S,
          finiteHistLocalityPacketEncodeBHist T,
          finiteHistLocalityPacketEncodeBHist C,
          finiteHistLocalityPacketEncodeBHist Q,
          finiteHistLocalityPacketEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro H0 H1 L I S T C Q N
  rfl

theorem FiniteHistLocalityPacketTransportStability
    {H0 H1 L I S T C Q N replay : BHist} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
      [H0, H1, L, I, S, T, C, Q, N] →
      Cont T C replay →
        UnaryHistory T →
          UnaryHistory C →
            UnaryHistory replay ∧ Cont T C replay := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro hfields transportReplay transportUnary replayRowUnary
  cases hfields
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportUnary replayRowUnary transportReplay
  exact ⟨replayUnary, transportReplay⟩

theorem FiniteHistLocalityPacketObligationSurface
    {H0 H1 L I S T C Q N replay : BHist} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
      [H0, H1, L, I, S, T, C, Q, N] →
      Cont H0 H1 L →
        Cont T C replay →
          UnaryHistory H0 →
            UnaryHistory H1 →
              UnaryHistory T →
                UnaryHistory C →
                  UnaryHistory H0 ∧ UnaryHistory H1 ∧ UnaryHistory L ∧
                    UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory replay ∧
                      Cont H0 H1 L ∧ Cont T C replay ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro hfields localityRoute replayRoute h0Unary h1Unary transportUnary replayRowUnary
  cases hfields
  have localityUnary : UnaryHistory L :=
    unary_cont_closed h0Unary h1Unary localityRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportUnary replayRowUnary replayRoute
  exact
    ⟨h0Unary, h1Unary, localityUnary, transportUnary, replayRowUnary, replayUnary,
      localityRoute, replayRoute, hsame_refl N⟩

theorem FiniteHistLocalityPacketNoGlobalSyncRefusal
    {H0 H1 L I S T C Q N localityReplay symmetryReplay : BHist} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
      [H0, H1, L, I, S, T, C, Q, N] →
      Cont H0 H1 L →
        Cont I S symmetryReplay →
          Cont L T localityReplay →
            UnaryHistory H0 →
              UnaryHistory H1 →
                UnaryHistory I →
                  UnaryHistory S →
                    UnaryHistory T →
                      UnaryHistory L ∧
                        UnaryHistory symmetryReplay ∧
                          UnaryHistory localityReplay ∧
                            Cont H0 H1 L ∧
                              Cont I S symmetryReplay ∧
                                Cont L T localityReplay ∧ hsame Q Q := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro hfields localityRoute symmetryRoute localityReplayRoute h0Unary h1Unary
    invariantUnary symmetryUnary transportUnary
  cases hfields
  have localityUnary : UnaryHistory L :=
    unary_cont_closed h0Unary h1Unary localityRoute
  have symmetryReplayUnary : UnaryHistory symmetryReplay :=
    unary_cont_closed invariantUnary symmetryUnary symmetryRoute
  have localityReplayUnary : UnaryHistory localityReplay :=
    unary_cont_closed localityUnary transportUnary localityReplayRoute
  exact
    ⟨localityUnary, symmetryReplayUnary, localityReplayUnary, localityRoute,
      symmetryRoute, localityReplayRoute, hsame_refl Q⟩

theorem FiniteHistLocalityPacket_consumer_handoff [AskSetup] [PackageSetup]
    {H0 H1 L I S T C Q N localityReplay consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
      [H0, H1, L, I, S, T, C, Q, N] →
      Cont H0 H1 L →
        Cont L T localityReplay →
          Cont localityReplay C consumerRead →
            PkgSig bundle consumerRead pkg →
              UnaryHistory H0 →
                UnaryHistory H1 →
                  UnaryHistory T →
                    UnaryHistory C →
                      SemanticNameCert
                          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                          (fun row : BHist => hsame row L ∨ hsame row localityReplay ∨
                            hsame row consumerRead)
                          (fun row : BHist =>
                            hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
                          hsame ∧
                        UnaryHistory L ∧ UnaryHistory localityReplay ∧
                          UnaryHistory consumerRead ∧ Cont H0 H1 L ∧
                            Cont L T localityReplay ∧
                              Cont localityReplay C consumerRead ∧
                                PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro hfields localityRoute replayRoute consumerRoute consumerPkg h0Unary h1Unary
    transportUnary consumerUnary
  cases hfields
  have localityUnary : UnaryHistory L :=
    unary_cont_closed h0Unary h1Unary localityRoute
  have replayUnary : UnaryHistory localityReplay :=
    unary_cont_closed localityUnary transportUnary replayRoute
  have readUnary : UnaryHistory consumerRead :=
    unary_cont_closed replayUnary consumerUnary consumerRoute
  have sourceAtRead : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, readUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row L ∨ hsame row localityReplay ∨
            hsame row consumerRead)
          (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨cert, localityUnary, replayUnary, readUnary, localityRoute, replayRoute,
      consumerRoute, consumerPkg⟩

theorem FiniteHistLocalityPacketConsumerHandoff
    {H0 H1 L I S T C Q N localityReplay symmetryReplay handoff : BHist} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
      [H0, H1, L, I, S, T, C, Q, N] →
      Cont H0 H1 L →
        Cont I S symmetryReplay →
          Cont L T localityReplay →
            Cont localityReplay C handoff →
              UnaryHistory H0 →
                UnaryHistory H1 →
                  UnaryHistory I →
                    UnaryHistory S →
                      UnaryHistory T →
                        UnaryHistory C →
                          UnaryHistory L ∧
                            UnaryHistory symmetryReplay ∧
                              UnaryHistory localityReplay ∧
                                UnaryHistory handoff ∧
                                  Cont H0 H1 L ∧
                                    Cont I S symmetryReplay ∧
                                      Cont L T localityReplay ∧
                                        Cont localityReplay C handoff ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro hfields localityRoute symmetryRoute localityReplayRoute handoffRoute h0Unary h1Unary
    invariantUnary symmetryUnary transportUnary replayUnary
  cases hfields
  have localityUnary : UnaryHistory L :=
    unary_cont_closed h0Unary h1Unary localityRoute
  have symmetryReplayUnary : UnaryHistory symmetryReplay :=
    unary_cont_closed invariantUnary symmetryUnary symmetryRoute
  have localityReplayUnary : UnaryHistory localityReplay :=
    unary_cont_closed localityUnary transportUnary localityReplayRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed localityReplayUnary replayUnary handoffRoute
  exact
    ⟨localityUnary, symmetryReplayUnary, localityReplayUnary, handoffUnary,
      localityRoute, symmetryRoute, localityReplayRoute, handoffRoute, hsame_refl N⟩

theorem FiniteHistLocalityPacketCarrier_obligation_closure_package
    {H0 H1 L I S T C Q N localityRead invariantRead replayRead : BHist} :
    finiteHistLocalityPacketFields (FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N) =
        [H0, H1, L, I, S, T, C, Q, N] →
      Cont H0 H1 localityRead →
        Cont L I invariantRead →
          Cont T C replayRead →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row replayRead ∧
                    ∃ packet : FiniteHistLocalityPacketUp,
                      packet = FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N ∧
                        finiteHistLocalityPacketFields packet =
                          [H0, H1, L, I, S, T, C, Q, N])
                (fun row : BHist =>
                  Cont H0 H1 localityRead ∧ Cont L I invariantRead ∧ Cont T C row)
                (fun row : BHist =>
                  hsame row replayRead ∧ Cont T C replayRead ∧ hsame Q Q)
                hsame ∧
              Cont H0 H1 localityRead ∧ Cont L I invariantRead ∧ Cont T C replayRead := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro fieldsExact localityRoute invariantRoute replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨replayRead, hsame_refl replayRead,
              FiniteHistLocalityPacketUp.mk H0 H1 L I S T C Q N, rfl, fieldsExact⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨localityRoute, invariantRoute,
            cont_result_hsame_transport replayRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, replayRoute, hsame_refl Q⟩
    }
  · exact ⟨localityRoute, invariantRoute, replayRoute⟩

end BEDC.Derived.FiniteHistLocalityPacketUp
