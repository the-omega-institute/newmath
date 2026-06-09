import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PerronIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PerronIntegralUp : Type where
  | mk (G R D M m U L E H C Q N : BHist) : PerronIntegralUp
  deriving DecidableEq

def PerronIntegralTasteGate_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: PerronIntegralTasteGate_encodeBHist h
  | BHist.e1 h => BMark.b1 :: PerronIntegralTasteGate_encodeBHist h

def PerronIntegralTasteGate_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (PerronIntegralTasteGate_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (PerronIntegralTasteGate_decodeBHist tail)

private theorem PerronIntegralTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def PerronIntegralTasteGate_fields : PerronIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PerronIntegralUp.mk G R D M m U L E H C Q N => [G, R, D, M, m, U, L, E, H, C, Q, N]

def PerronIntegralTasteGate_toEventFlow : PerronIntegralUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (PerronIntegralTasteGate_fields x).map PerronIntegralTasteGate_encodeBHist

private def PerronIntegralTasteGate_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => PerronIntegralTasteGate_eventAt index rest

def PerronIntegralTasteGate_fromEventFlow (flow : EventFlow) : Option PerronIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PerronIntegralUp.mk
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 0 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 1 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 2 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 3 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 4 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 5 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 6 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 7 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 8 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 9 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 10 flow))
      (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_eventAt 11 flow)))

private theorem PerronIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PerronIntegralUp,
      PerronIntegralTasteGate_fromEventFlow (PerronIntegralTasteGate_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G R D M m U L E H C Q N =>
      change
        some
          (PerronIntegralUp.mk
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist G))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist R))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist D))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist M))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist m))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist U))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist L))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist E))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist H))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist C))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist Q))
            (PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist N))) =
          some (PerronIntegralUp.mk G R D M m U L E H C Q N)
      rw [PerronIntegralTasteGate_single_carrier_alignment_decode G,
        PerronIntegralTasteGate_single_carrier_alignment_decode R,
        PerronIntegralTasteGate_single_carrier_alignment_decode D,
        PerronIntegralTasteGate_single_carrier_alignment_decode M,
        PerronIntegralTasteGate_single_carrier_alignment_decode m,
        PerronIntegralTasteGate_single_carrier_alignment_decode U,
        PerronIntegralTasteGate_single_carrier_alignment_decode L,
        PerronIntegralTasteGate_single_carrier_alignment_decode E,
        PerronIntegralTasteGate_single_carrier_alignment_decode H,
        PerronIntegralTasteGate_single_carrier_alignment_decode C,
        PerronIntegralTasteGate_single_carrier_alignment_decode Q,
        PerronIntegralTasteGate_single_carrier_alignment_decode N]

private theorem PerronIntegralTasteGate_toEventFlow_injective {x y : PerronIntegralUp} :
    PerronIntegralTasteGate_toEventFlow x = PerronIntegralTasteGate_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      PerronIntegralTasteGate_fromEventFlow (PerronIntegralTasteGate_toEventFlow x) =
        PerronIntegralTasteGate_fromEventFlow (PerronIntegralTasteGate_toEventFlow y) :=
    congrArg PerronIntegralTasteGate_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PerronIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PerronIntegralTasteGate_single_carrier_alignment_round_trip y)))

private theorem PerronIntegralTasteGate_field_faithful :
    ∀ x y : PerronIntegralUp,
      PerronIntegralTasteGate_fields x = PerronIntegralTasteGate_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 R1 D1 M1 m1 U1 L1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk G2 R2 D2 M2 m2 U2 L2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance perronIntegralBHistCarrier : BHistCarrier PerronIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := PerronIntegralTasteGate_toEventFlow
  fromEventFlow := PerronIntegralTasteGate_fromEventFlow

instance perronIntegralChapterTasteGate : ChapterTasteGate PerronIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change PerronIntegralTasteGate_fromEventFlow (PerronIntegralTasteGate_toEventFlow x) =
      some x
    exact PerronIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PerronIntegralTasteGate_toEventFlow_injective heq)

instance perronIntegralFieldFaithful : FieldFaithful PerronIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := PerronIntegralTasteGate_fields
  field_faithful := PerronIntegralTasteGate_field_faithful

instance perronIntegralNontrivial : Nontrivial PerronIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PerronIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PerronIntegralUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PerronIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  perronIntegralChapterTasteGate

def taste_gate_witness : FieldFaithful PerronIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  perronIntegralFieldFaithful

theorem PerronIntegralTasteGate_single_carrier_alignment :
    (forall h : BHist,
      PerronIntegralTasteGate_decodeBHist (PerronIntegralTasteGate_encodeBHist h) = h) ∧
      PerronIntegralTasteGate_fields
        (PerronIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨PerronIntegralTasteGate_single_carrier_alignment_decode, rfl⟩

theorem PerronIntegralNamecertObligations [AskSetup] [PackageSetup]
    {G R D M m U L E H C Q N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G -> UnaryHistory R -> UnaryHistory D -> UnaryHistory M ->
      UnaryHistory m -> UnaryHistory H -> UnaryHistory C -> UnaryHistory Q ->
        UnaryHistory N -> Cont G R D -> Cont D M U -> Cont D m L -> Cont U L E ->
          Cont H C Q -> PkgSig bundle Q pkg -> PkgSig bundle N pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row G ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨
                    hsame row m ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
                      Cont G R D ∨ Cont U L E)
                (fun row : BHist =>
                  PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧ hsame row N)
                hsame ∧ UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _unaryG _unaryR unaryD unaryM unarym _unaryH _unaryC _unaryQ unaryN
    _gaugeRoute upperRoute lowerRoute sealRoute _provenanceRoute provenancePkg namePkg
  have upperUnary : UnaryHistory U :=
    unary_cont_closed unaryD unaryM upperRoute
  have lowerUnary : UnaryHistory L :=
    unary_cont_closed unaryD unarym lowerRoute
  have sealUnary : UnaryHistory E :=
    unary_cont_closed upperUnary lowerUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row R ∨ hsame row D ∨ hsame row M ∨ hsame row m ∨
              hsame row U ∨ hsame row L ∨ hsame row E ∨ Cont G R D ∨ Cont U L E)
          (fun row : BHist =>
            PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧ hsame row N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr sealRoute))))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, namePkg, source.left⟩
  }
  exact ⟨cert, upperUnary, lowerUnary, sealUnary⟩

end BEDC.Derived.PerronIntegralUp
