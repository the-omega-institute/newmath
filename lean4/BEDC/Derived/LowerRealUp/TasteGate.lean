import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LowerRealUp : Type where
  | mk (L W R E H C P N : BHist) : LowerRealUp
  deriving DecidableEq

def lowerRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowerRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowerRealEncodeBHist h

def lowerRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowerRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowerRealDecodeBHist tail)

private theorem LowerRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lowerRealDecodeBHist (lowerRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lowerRealFields : LowerRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerRealUp.mk L W R E H C P N => [L, W, R, E, H, C, P, N]

def lowerRealToEventFlow : LowerRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lowerRealFields x).map lowerRealEncodeBHist

private def LowerRealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LowerRealTasteGate_single_carrier_alignment_eventAt index rest

def lowerRealFromEventFlow (ef : EventFlow) : Option LowerRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LowerRealUp.mk
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem LowerRealTasteGate_single_carrier_alignment_round_trip
    (x : LowerRealUp) :
    lowerRealFromEventFlow (lowerRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L W R E H C P N =>
      change
        some
          (LowerRealUp.mk
            (lowerRealDecodeBHist (lowerRealEncodeBHist L))
            (lowerRealDecodeBHist (lowerRealEncodeBHist W))
            (lowerRealDecodeBHist (lowerRealEncodeBHist R))
            (lowerRealDecodeBHist (lowerRealEncodeBHist E))
            (lowerRealDecodeBHist (lowerRealEncodeBHist H))
            (lowerRealDecodeBHist (lowerRealEncodeBHist C))
            (lowerRealDecodeBHist (lowerRealEncodeBHist P))
            (lowerRealDecodeBHist (lowerRealEncodeBHist N))) =
          some (LowerRealUp.mk L W R E H C P N)
      rw [LowerRealTasteGate_single_carrier_alignment_decode_encode L,
        LowerRealTasteGate_single_carrier_alignment_decode_encode W,
        LowerRealTasteGate_single_carrier_alignment_decode_encode R,
        LowerRealTasteGate_single_carrier_alignment_decode_encode E,
        LowerRealTasteGate_single_carrier_alignment_decode_encode H,
        LowerRealTasteGate_single_carrier_alignment_decode_encode C,
        LowerRealTasteGate_single_carrier_alignment_decode_encode P,
        LowerRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LowerRealUp} :
    lowerRealToEventFlow x = lowerRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowerRealFromEventFlow (lowerRealToEventFlow x) =
        lowerRealFromEventFlow (lowerRealToEventFlow y) :=
    congrArg lowerRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LowerRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LowerRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem LowerRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LowerRealUp, lowerRealFields x = lowerRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lowerRealBHistCarrier : BHistCarrier LowerRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowerRealToEventFlow
  fromEventFlow := lowerRealFromEventFlow

instance lowerRealChapterTasteGate : ChapterTasteGate LowerRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowerRealFromEventFlow (lowerRealToEventFlow x) = some x
    exact LowerRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LowerRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, lowerRealDecodeBHist (lowerRealEncodeBHist h) = h) ∧
      (∀ x : LowerRealUp, lowerRealFromEventFlow (lowerRealToEventFlow x) = some x) ∧
        (∀ x y : LowerRealUp, lowerRealToEventFlow x = lowerRealToEventFlow y → x = y) ∧
          lowerRealEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LowerRealUp, lowerRealFields x = lowerRealFields y → x = y) ∧
              (∃ x y : LowerRealUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LowerRealTasteGate_single_carrier_alignment_decode_encode,
      LowerRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      LowerRealTasteGate_single_carrier_alignment_fields_faithful,
      ⟨LowerRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        LowerRealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

theorem LowerRealCarrier_namecert_obligations (x : LowerRealUp) :
    ∃ L0 W R E H C P N : BHist,
      x = LowerRealUp.mk L0 W R E H C P N ∧
        lowerRealFields x = [L0, W, R, E, H, C, P, N] ∧
          lowerRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark NameCert
  cases x with
  | mk L0 W R E H C P N =>
      exact ⟨L0, W, R, E, H, C, P, N, rfl, rfl, rfl⟩

theorem LowerRealCarrier_realup_handoff
    {L0 W R E H C P N windowRead sealRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            Cont W R windowRead →
              Cont windowRead E sealRead →
                UnaryHistory windowRead ∧
                  UnaryHistory sealRead ∧
                    Cont W R windowRead ∧
                      Cont windowRead E sealRead ∧
                        hsame (lowerRealDecodeBHist (lowerRealEncodeBHist E)) E := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows windowUnary handoffUnary sealUnary windowRoute sealRoute
  cases fieldRows
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary handoffUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have sealDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist E)) E := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist E) = E
    exact LowerRealTasteGate_single_carrier_alignment_decode_encode E
  exact ⟨windowReadUnary, sealReadUnary, windowRoute, sealRoute, sealDecode⟩

theorem LowerRealCarrier_scoped_kernel_obligation
    {L0 W R E H C P N locatedRead rationalRead realRead scopedRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                Cont L0 W locatedRead ->
                  Cont locatedRead R rationalRead ->
                    Cont rationalRead E realRead ->
                      Cont realRead N scopedRead ->
                        UnaryHistory locatedRead ∧
                          UnaryHistory rationalRead ∧
                            UnaryHistory realRead ∧
                              UnaryHistory scopedRead ∧
                                Cont L0 W locatedRead ∧
                                  Cont locatedRead R rationalRead ∧
                                    Cont rationalRead E realRead ∧
                                      Cont realRead N scopedRead ∧
                                        hsame
                                          (lowerRealDecodeBHist (lowerRealEncodeBHist L0))
                                          L0 := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows l0Unary windowUnary rationalUnary realUnary nameUnary locatedRoute
    rationalRoute realRoute scopedRoute
  cases fieldRows
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed l0Unary windowUnary locatedRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed locatedUnary rationalUnary rationalRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary realUnary realRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed realReadUnary nameUnary scopedRoute
  have lowerDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist L0)) L0 := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist L0) = L0
    exact LowerRealTasteGate_single_carrier_alignment_decode_encode L0
  exact
    ⟨locatedUnary, rationalReadUnary, realReadUnary, scopedReadUnary, locatedRoute,
      rationalRoute, realRoute, scopedRoute, lowerDecode⟩

theorem LowerRealPublicConsumer_export [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerRead rationalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont L0 W lowerRead ->
                Cont lowerRead R rationalRead ->
                  Cont rationalRead E realRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle realRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row L0 ∨ hsame row W ∨ hsame row R ∨
                                hsame row E ∨ hsame row realRead)
                            (fun row : BHist =>
                              hsame row realRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle realRead pkg)
                            hsame ∧
                          UnaryHistory lowerRead ∧
                            UnaryHistory rationalRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldRows l0Unary wUnary rUnary eUnary lowerRoute rationalRoute realRoute pPkg realPkg
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed l0Unary wUnary lowerRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row realRead)
          (fun row : BHist =>
            hsame row realRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pPkg, realPkg⟩
  }
  exact ⟨cert, lowerUnary, rationalUnary, realUnary⟩

end BEDC.Derived.LowerRealUp
