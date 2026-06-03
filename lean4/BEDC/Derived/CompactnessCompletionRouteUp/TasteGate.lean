import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactnessCompletionRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactnessCompletionRouteUp : Type where
  | mk (M T C W R E H Q P N : BHist) : CompactnessCompletionRouteUp
  deriving DecidableEq

def compactnessCompletionRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactnessCompletionRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactnessCompletionRouteEncodeBHist h

def compactnessCompletionRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactnessCompletionRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactnessCompletionRouteDecodeBHist tail)

private theorem compactnessCompletionRoute_decode_encode_bhist :
    ∀ h : BHist,
      compactnessCompletionRouteDecodeBHist
        (compactnessCompletionRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem compactnessCompletionRoute_mk_congr
    {M M' T T' C C' W W' R R' E E' H H' Q Q' P P' N N' : BHist}
    (hM : M' = M) (hT : T' = T) (hC : C' = C) (hW : W' = W)
    (hR : R' = R) (hE : E' = E) (hH : H' = H) (hQ : Q' = Q)
    (hP : P' = P) (hN : N' = N) :
    CompactnessCompletionRouteUp.mk M' T' C' W' R' E' H' Q' P' N' =
      CompactnessCompletionRouteUp.mk M T C W R E H Q P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hT
  cases hC
  cases hW
  cases hR
  cases hE
  cases hH
  cases hQ
  cases hP
  cases hN
  rfl

def compactnessCompletionRouteFields :
    CompactnessCompletionRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactnessCompletionRouteUp.mk M T C W R E H Q P N =>
      [M, T, C, W, R, E, H, Q, P, N]

def compactnessCompletionRouteToEventFlow :
    CompactnessCompletionRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactnessCompletionRouteFields x).map
      compactnessCompletionRouteEncodeBHist

private def compactnessCompletionRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | _, [] => []
  | 0, row :: _ => row
  | n + 1, _ :: rows => compactnessCompletionRouteEventAtDefault n rows

def compactnessCompletionRouteFromEventFlow
    (ef : EventFlow) : Option CompactnessCompletionRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef.length with
  | 10 =>
      some
        (CompactnessCompletionRouteUp.mk
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 0 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 1 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 2 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 3 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 4 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 5 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 6 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 7 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 8 ef))
          (compactnessCompletionRouteDecodeBHist
            (compactnessCompletionRouteEventAtDefault 9 ef)))
  | _ => none

private theorem compactnessCompletionRoute_round_trip :
    ∀ x : CompactnessCompletionRouteUp,
      compactnessCompletionRouteFromEventFlow
        (compactnessCompletionRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T C W R E H Q P N =>
      change
        some
          (CompactnessCompletionRouteUp.mk
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist M))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist T))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist C))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist W))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist R))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist E))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist H))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist Q))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist P))
            (compactnessCompletionRouteDecodeBHist
              (compactnessCompletionRouteEncodeBHist N))) =
          some (CompactnessCompletionRouteUp.mk M T C W R E H Q P N)
      exact
        congrArg some
          (compactnessCompletionRoute_mk_congr
            (compactnessCompletionRoute_decode_encode_bhist M)
            (compactnessCompletionRoute_decode_encode_bhist T)
            (compactnessCompletionRoute_decode_encode_bhist C)
            (compactnessCompletionRoute_decode_encode_bhist W)
            (compactnessCompletionRoute_decode_encode_bhist R)
            (compactnessCompletionRoute_decode_encode_bhist E)
            (compactnessCompletionRoute_decode_encode_bhist H)
            (compactnessCompletionRoute_decode_encode_bhist Q)
            (compactnessCompletionRoute_decode_encode_bhist P)
            (compactnessCompletionRoute_decode_encode_bhist N))

private theorem compactnessCompletionRouteToEventFlow_injective
    {x y : CompactnessCompletionRouteUp} :
    compactnessCompletionRouteToEventFlow x =
      compactnessCompletionRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactnessCompletionRouteFromEventFlow
          (compactnessCompletionRouteToEventFlow x) =
        compactnessCompletionRouteFromEventFlow
          (compactnessCompletionRouteToEventFlow y) :=
    congrArg compactnessCompletionRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactnessCompletionRoute_round_trip x).symm
      (Eq.trans hread (compactnessCompletionRoute_round_trip y)))

instance compactnessCompletionRouteBHistCarrier :
    BHistCarrier CompactnessCompletionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactnessCompletionRouteToEventFlow
  fromEventFlow := compactnessCompletionRouteFromEventFlow

instance compactnessCompletionRouteChapterTasteGate :
    ChapterTasteGate CompactnessCompletionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactnessCompletionRouteFromEventFlow
        (compactnessCompletionRouteToEventFlow x) = some x
    exact compactnessCompletionRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactnessCompletionRouteToEventFlow_injective heq)

theorem CompactnessCompletionRouteTasteGate_single_carrier_alignment :
    ChapterTasteGate CompactnessCompletionRouteUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact compactnessCompletionRouteChapterTasteGate

theorem CompactnessCompletionRouteCarrier_namecert_obligations
    (x : CompactnessCompletionRouteUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ compactnessCompletionRouteFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ compactnessCompletionRouteFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ compactnessCompletionRouteFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk M T C W R E H Q P N =>
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

theorem CompactnessCompletionRouteNonescape {M T C W R E H Q P N : BHist} :
    SemanticNameCert
        (fun row : BHist => hsame row (append (append M T) C))
        (fun row : BHist =>
          hsame row M ∨ hsame row T ∨ hsame row C ∨ hsame row W ∨
            hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row Q ∨
              hsame row P ∨ hsame row N ∨ hsame row (append (append M T) C))
        (fun row : BHist =>
          hsame row (append (append M T) C) ∧
            Cont M T (append M T) ∧
              Cont (append M T) C (append (append M T) C))
        hsame ∧
      Cont M T (append M T) ∧
        Cont (append M T) C (append (append M T) C) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  refine ⟨?_, rfl, rfl⟩
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨append (append M T) C, hsame_refl (append (append M T) C)⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other same
    exact hsame_symm same
  · intro _row _other _third same₁ same₂
    exact hsame_trans same₁ same₂
  · intro _row _other same source
    exact hsame_trans (hsame_symm same) source
  · intro _row source
    exact
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source)))))))))
  · intro _row source
    exact ⟨source, rfl, rfl⟩

theorem CompactnessCompletionRouteFiniteNetHandoff {M T C W R E H Q P N : BHist} :
    Cont T W (append T W) ∧
      Cont (append T W) R (append (append T W) R) ∧
        SemanticNameCert
          (fun row : BHist => hsame row (append (append T W) R))
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row Q ∨
                hsame row P ∨ hsame row N ∨ hsame row (append T W) ∨
                  hsame row (append (append T W) R))
          (fun row : BHist =>
            hsame row (append (append T W) R) ∧
              Cont T W (append T W) ∧
                Cont (append T W) R (append (append T W) R))
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  refine ⟨rfl, rfl, ?_⟩
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨append (append T W) R, hsame_refl (append (append T W) R)⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other same
    exact hsame_symm same
  · intro _row _other _third same₁ same₂
    exact hsame_trans same₁ same₂
  · intro _row _other same source
    exact hsame_trans (hsame_symm same) source
  · intro _row source
    exact
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source))))))))))
  · intro _row source
    exact ⟨source, rfl, rfl⟩

end BEDC.Derived.CompactnessCompletionRouteUp
