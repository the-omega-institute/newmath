import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClusterFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClusterFilterUp : Type where
  | mk (F M T W R E A H C P N : BHist) : ClusterFilterUp
  deriving DecidableEq

def clusterFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: clusterFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: clusterFilterEncodeBHist h

def clusterFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (clusterFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (clusterFilterDecodeBHist tail)

private theorem clusterFilterDecode_encode_bhist :
    ∀ h : BHist, clusterFilterDecodeBHist (clusterFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def clusterFilterFields : ClusterFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClusterFilterUp.mk F M T W R E A H C P N => [F, M, T, W, R, E, A, H, C, P, N]

def clusterFilterToEventFlow : ClusterFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (clusterFilterFields x).map clusterFilterEncodeBHist

private def clusterFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => clusterFilterEventAtDefault index rest

def clusterFilterFromEventFlow (ef : EventFlow) : Option ClusterFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClusterFilterUp.mk
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 0 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 1 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 2 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 3 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 4 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 5 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 6 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 7 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 8 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 9 ef))
      (clusterFilterDecodeBHist (clusterFilterEventAtDefault 10 ef)))

private theorem clusterFilter_round_trip :
    ∀ x : ClusterFilterUp, clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M T W R E A H C P N =>
      change
        some
          (ClusterFilterUp.mk
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist F))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist M))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist T))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist W))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist R))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist E))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist A))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist H))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist C))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist P))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist N))) =
          some (ClusterFilterUp.mk F M T W R E A H C P N)
      rw [clusterFilterDecode_encode_bhist F, clusterFilterDecode_encode_bhist M,
        clusterFilterDecode_encode_bhist T, clusterFilterDecode_encode_bhist W,
        clusterFilterDecode_encode_bhist R, clusterFilterDecode_encode_bhist E,
        clusterFilterDecode_encode_bhist A, clusterFilterDecode_encode_bhist H,
        clusterFilterDecode_encode_bhist C, clusterFilterDecode_encode_bhist P,
        clusterFilterDecode_encode_bhist N]

private theorem clusterFilterToEventFlow_injective {x y : ClusterFilterUp} :
    clusterFilterToEventFlow x = clusterFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      clusterFilterFromEventFlow (clusterFilterToEventFlow x) =
        clusterFilterFromEventFlow (clusterFilterToEventFlow y) :=
    congrArg clusterFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (clusterFilter_round_trip x).symm
      (Eq.trans hread (clusterFilter_round_trip y)))

instance clusterFilterBHistCarrier : BHistCarrier ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := clusterFilterToEventFlow
  fromEventFlow := clusterFilterFromEventFlow

instance clusterFilterChapterTasteGate : ChapterTasteGate ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x
    exact clusterFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (clusterFilterToEventFlow_injective heq)

instance clusterFilterNontrivial : Nontrivial ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClusterFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClusterFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClusterFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  clusterFilterChapterTasteGate

theorem ClusterFilterUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, clusterFilterDecodeBHist (clusterFilterEncodeBHist h) = h) ∧
      (∀ x : ClusterFilterUp,
        clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x) ∧
        (∀ x y : ClusterFilterUp,
          clusterFilterToEventFlow x = clusterFilterToEventFlow y → x = y) ∧
          clusterFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate Nontrivial
  exact
    ⟨clusterFilterDecode_encode_bhist, clusterFilter_round_trip,
      (fun _ _ heq => clusterFilterToEventFlow_injective heq), rfl⟩

theorem ClusterFilterCarrier_namecert_obligations (x : ClusterFilterUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist => hsame row localCert ∧ localCert ∈ clusterFilterFields x)
        (fun row : BHist => hsame row localCert ∧ localCert ∈ clusterFilterFields x)
        (fun row : BHist => hsame row localCert ∧ localCert ∈ clusterFilterFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk F M T W R E A H C P N =>
      refine ⟨N, ?_⟩
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact
          ⟨N, hsame_refl N,
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.tail _ <|
                          List.Mem.tail _ <|
                            List.Mem.tail _ <|
                              List.Mem.tail _ <| List.Mem.head _⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _other _third same₁ same₂
        exact hsame_trans same₁ same₂
      · intro _row _other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
      · intro _row source
        exact source
      · intro _row source
        exact source

end BEDC.Derived.ClusterFilterUp
