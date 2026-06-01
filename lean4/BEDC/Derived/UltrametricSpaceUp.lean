import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UltrametricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UltrametricSpaceUp : Type where
  | mk (M V T B E H K P N : BHist) : UltrametricSpaceUp
  deriving DecidableEq

def ultrametricSpaceFields : UltrametricSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UltrametricSpaceUp.mk M V T B E H K P N => [M, V, T, B, E, H, K, P, N]

def ultrametricSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ultrametricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ultrametricSpaceEncodeBHist h

def ultrametricSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ultrametricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ultrametricSpaceDecodeBHist tail)

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ultrametricSpaceToEventFlow : UltrametricSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ultrametricSpaceFields x).map ultrametricSpaceEncodeBHist

private def ultrametricSpaceRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => ultrametricSpaceRawAt n rest

def ultrametricSpaceFromEventFlow (flow : EventFlow) : Option UltrametricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UltrametricSpaceUp.mk
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 0 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 1 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 2 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 3 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 4 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 5 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 6 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 7 flow))
      (ultrametricSpaceDecodeBHist (ultrametricSpaceRawAt 8 flow)))

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : UltrametricSpaceUp) :
    ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M V T B E H K P N =>
      change
        some
          (UltrametricSpaceUp.mk
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist M))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist V))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist T))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist B))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist E))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist H))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist K))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist P))
            (ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist N))) =
          some (UltrametricSpaceUp.mk M V T B E H K P N)
      rw [UltrametricSpaceTasteGate_single_carrier_alignment_decode M,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode V,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode T,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode B,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode E,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode H,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode K,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode P,
        UltrametricSpaceTasteGate_single_carrier_alignment_decode N]

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UltrametricSpaceUp} :
    ultrametricSpaceToEventFlow x = ultrametricSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) =
        ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow y) :=
    congrArg ultrametricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UltrametricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UltrametricSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem UltrametricSpaceTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : UltrametricSpaceUp,
      ultrametricSpaceFields x = ultrametricSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Ma Va Ta Ba Ea Ha Ka Pa Na =>
      cases y with
      | mk Mb Vb Tb Bb Eb Hb Kb Pb Nb =>
          cases hfields
          rfl

instance ultrametricSpaceBHistCarrier : BHistCarrier UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ultrametricSpaceToEventFlow
  fromEventFlow := ultrametricSpaceFromEventFlow

instance ultrametricSpaceChapterTasteGate : ChapterTasteGate UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x
    exact UltrametricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ultrametricSpaceFieldFaithful : FieldFaithful UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ultrametricSpaceFields
  field_faithful := UltrametricSpaceTasteGate_single_carrier_alignment_fields_faithful

instance ultrametricSpaceNontrivial : Nontrivial UltrametricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UltrametricSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UltrametricSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem UltrametricSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UltrametricSpaceUp) ∧
      Nonempty (FieldFaithful UltrametricSpaceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial UltrametricSpaceUp) ∧
      (∀ h : BHist, ultrametricSpaceDecodeBHist (ultrametricSpaceEncodeBHist h) = h) ∧
      (∀ x : UltrametricSpaceUp,
        ultrametricSpaceFromEventFlow (ultrametricSpaceToEventFlow x) = some x) ∧
      (∀ x y : UltrametricSpaceUp,
        ultrametricSpaceToEventFlow x = ultrametricSpaceToEventFlow y -> x = y) ∧
      ultrametricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨ultrametricSpaceChapterTasteGate⟩, ⟨ultrametricSpaceFieldFaithful⟩,
      ⟨ultrametricSpaceNontrivial⟩,
      UltrametricSpaceTasteGate_single_carrier_alignment_decode,
      UltrametricSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => UltrametricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

private theorem UltrametricSpaceStrongTriangle_handoff_encode_display
    (h : BHist) :
    ∀ m, List.Mem m (ultrametricSpaceEncodeBHist h) ->
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      intro m hm
      cases hm
  | e0 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inl rfl
      | tail _ hmTail =>
          exact ih m hmTail
  | e1 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inr rfl
      | tail _ hmTail =>
          exact ih m hmTail

private theorem UltrametricSpaceStrongTriangle_handoff_flow_display
    (rows : List BHist) :
    ∀ w m, List.Mem w (rows.map ultrametricSpaceEncodeBHist) -> List.Mem m w ->
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction rows with
  | nil =>
      intro w m hw _hm
      cases hw
  | cons h rows ih =>
      intro w m hw hm
      cases hw with
      | head =>
          exact UltrametricSpaceStrongTriangle_handoff_encode_display h m hm
      | tail _ hwTail =>
          exact ih w m hwTail hm

theorem UltrametricSpaceStrongTriangle_handoff (x : UltrametricSpaceUp) :
    (∃ rows : List BHist, rows = ultrametricSpaceFields x) ∧
      (∀ w m, List.Mem w (ultrametricSpaceToEventFlow x) -> List.Mem m w ->
        m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨ultrametricSpaceFields x, rfl⟩
  · intro w m hw hm
    exact UltrametricSpaceStrongTriangle_handoff_flow_display
      (ultrametricSpaceFields x) w m hw hm

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UltrametricSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (U : UltrametricSpaceUp)
    {M V T B E H K P N comparisonRead triangleRead ballRead exampleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ultrametricSpaceFields U = [M, V, T, B, E, H, K, P, N] ->
      UnaryHistory M -> UnaryHistory V -> UnaryHistory T -> UnaryHistory B -> UnaryHistory E ->
        Cont M V comparisonRead ->
          Cont comparisonRead T triangleRead ->
            Cont triangleRead B ballRead ->
              Cont ballRead E exampleRead ->
                PkgSig bundle P pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row exampleRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row V ∨ hsame row T ∨ hsame row B ∨
                          hsame row E ∨ Cont M V comparisonRead ∨
                            Cont comparisonRead T triangleRead ∨ Cont triangleRead B ballRead ∨
                              Cont ballRead E exampleRead)
                      (fun row : BHist => PkgSig bundle P pkg ∧ hsame row exampleRead)
                      hsame ∧ UnaryHistory comparisonRead ∧ UnaryHistory triangleRead ∧
                    UnaryHistory ballRead ∧ UnaryHistory exampleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _fields metricUnary comparisonUnary triangleUnary ballUnary exampleUnary
    comparisonRoute triangleRoute ballRoute exampleRoute provenancePkg
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed metricUnary comparisonUnary comparisonRoute
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed comparisonReadUnary triangleUnary triangleRoute
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed triangleReadUnary ballUnary ballRoute
  have exampleReadUnary : UnaryHistory exampleRead :=
    unary_cont_closed ballReadUnary exampleUnary exampleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exampleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row V ∨ hsame row T ∨ hsame row B ∨
              hsame row E ∨ Cont M V comparisonRead ∨
                Cont comparisonRead T triangleRead ∨ Cont triangleRead B ballRead ∨
                  Cont ballRead E exampleRead)
          (fun row : BHist => PkgSig bundle P pkg ∧ hsame row exampleRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exampleRead ⟨hsame_refl exampleRead, exampleReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr exampleRoute)))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨cert, comparisonReadUnary, triangleReadUnary, ballReadUnary, exampleReadUnary⟩

theorem UltrametricSpaceRootStrongTriangleWindow [AskSetup] [PackageSetup]
    (U : UltrametricSpaceUp) {M V T B E H K P N comparisonRead triangleRead : BHist} :
    ultrametricSpaceFields U = [M, V, T, B, E, H, K, P, N] ->
      UnaryHistory M ->
        UnaryHistory V ->
          UnaryHistory T ->
            Cont M V comparisonRead ->
              Cont comparisonRead T triangleRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row triangleRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row V ∨ hsame row T ∨
                        Cont M V comparisonRead ∨ Cont comparisonRead T triangleRead)
                    (fun row : BHist => UnaryHistory row ∧ hsame row triangleRead)
                    hsame ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory triangleRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro _fields metricUnary comparisonUnary triangleUnary comparisonRoute triangleRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed metricUnary comparisonUnary comparisonRoute
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed comparisonReadUnary triangleUnary triangleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row triangleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row V ∨ hsame row T ∨
              Cont M V comparisonRead ∨ Cont comparisonRead T triangleRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row triangleRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro triangleRead ⟨hsame_refl triangleRead, triangleReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr triangleRoute)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left⟩
  }
  exact ⟨cert, comparisonReadUnary, triangleReadUnary⟩

end BEDC.Derived.UltrametricSpaceUp
