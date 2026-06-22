import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BarRecursionUp

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

inductive BarRecursionUp : Type where
  | mk (S R W K Q E H C P N : BHist) : BarRecursionUp
  deriving DecidableEq

def barRecursionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: barRecursionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: barRecursionEncodeBHist h

def barRecursionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (barRecursionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (barRecursionDecodeBHist tail)

private theorem barRecursion_decode_encode_bhist :
    ∀ h : BHist, barRecursionDecodeBHist (barRecursionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def barRecursionFields : BarRecursionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BarRecursionUp.mk S R W K Q E H C P N => [S, R, W, K, Q, E, H, C, P, N]

def barRecursionToEventFlow : BarRecursionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (barRecursionFields x).map barRecursionEncodeBHist

private def barRecursionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => barRecursionEventAt index rest

def barRecursionFromEventFlow (ef : EventFlow) : Option BarRecursionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BarRecursionUp.mk
      (barRecursionDecodeBHist (barRecursionEventAt 0 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 1 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 2 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 3 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 4 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 5 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 6 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 7 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 8 ef))
      (barRecursionDecodeBHist (barRecursionEventAt 9 ef)))

private theorem barRecursion_round_trip (x : BarRecursionUp) :
    barRecursionFromEventFlow (barRecursionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R W K Q E H C P N =>
      change
        some
            (BarRecursionUp.mk
              (barRecursionDecodeBHist (barRecursionEncodeBHist S))
              (barRecursionDecodeBHist (barRecursionEncodeBHist R))
              (barRecursionDecodeBHist (barRecursionEncodeBHist W))
              (barRecursionDecodeBHist (barRecursionEncodeBHist K))
              (barRecursionDecodeBHist (barRecursionEncodeBHist Q))
              (barRecursionDecodeBHist (barRecursionEncodeBHist E))
              (barRecursionDecodeBHist (barRecursionEncodeBHist H))
              (barRecursionDecodeBHist (barRecursionEncodeBHist C))
              (barRecursionDecodeBHist (barRecursionEncodeBHist P))
              (barRecursionDecodeBHist (barRecursionEncodeBHist N))) =
          some (BarRecursionUp.mk S R W K Q E H C P N)
      rw [barRecursion_decode_encode_bhist S, barRecursion_decode_encode_bhist R,
        barRecursion_decode_encode_bhist W, barRecursion_decode_encode_bhist K,
        barRecursion_decode_encode_bhist Q, barRecursion_decode_encode_bhist E,
        barRecursion_decode_encode_bhist H, barRecursion_decode_encode_bhist C,
        barRecursion_decode_encode_bhist P, barRecursion_decode_encode_bhist N]

private theorem barRecursionToEventFlow_injective {x y : BarRecursionUp} :
    barRecursionToEventFlow x = barRecursionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      barRecursionFromEventFlow (barRecursionToEventFlow x) =
        barRecursionFromEventFlow (barRecursionToEventFlow y) :=
    congrArg barRecursionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (barRecursion_round_trip x).symm
      (Eq.trans hread (barRecursion_round_trip y)))

instance barRecursionBHistCarrier : BHistCarrier BarRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := barRecursionToEventFlow
  fromEventFlow := barRecursionFromEventFlow

instance barRecursionChapterTasteGate : ChapterTasteGate BarRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change barRecursionFromEventFlow (barRecursionToEventFlow x) = some x
    exact barRecursion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (barRecursionToEventFlow_injective heq)

theorem BarRecursionTasteGate_single_carrier_alignment :
    (∀ h : BHist, barRecursionDecodeBHist (barRecursionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BarRecursionUp) ∧
        Nonempty (ChapterTasteGate BarRecursionUp) ∧
          barRecursionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨barRecursion_decode_encode_bhist, ⟨barRecursionBHistCarrier⟩,
      ⟨barRecursionChapterTasteGate⟩, rfl⟩

def BarRecursionCarrier [AskSetup] [PackageSetup]
    (S R W K Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory K ∧
    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BarRecursionRealCompletionNonescape [AskSetup] [PackageSetup]
    {S R W K Q E H C P N stepWindow controlRead rationalRead realSeal localRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BarRecursionCarrier S R W K Q E H C P N bundle pkg ->
      Cont S R stepWindow ->
        Cont stepWindow W controlRead ->
          Cont controlRead K rationalRead ->
            Cont rationalRead Q realSeal ->
              Cont H C localRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle localRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row R ∨ hsame row W ∨ hsame row K ∨
                            hsame row Q ∨ hsame row E ∨ hsame row stepWindow ∨
                              hsame row controlRead ∨ hsame row rationalRead ∨
                                hsame row realSeal ∨ hsame row localRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S R stepWindow ∧
                            Cont stepWindow W controlRead ∧ Cont controlRead K rationalRead ∧
                              Cont rationalRead Q realSeal ∧ Cont H C localRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
                        hsame ∧
                      UnaryHistory stepWindow ∧ UnaryHistory controlRead ∧
                        UnaryHistory rationalRead ∧ UnaryHistory realSeal ∧
                          UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BarRecursionCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier stepRoute controlRoute rationalRoute realRoute localRoute provenancePkg localPkg
  obtain ⟨unaryS, unaryR, unaryW, unaryK, unaryQ, _unaryE, unaryH, unaryC, _unaryP,
    _unaryN, _carrierPkgP, _carrierPkgN⟩ := carrier
  have stepUnary : UnaryHistory stepWindow :=
    unary_cont_closed unaryS unaryR stepRoute
  have controlUnary : UnaryHistory controlRead :=
    unary_cont_closed stepUnary unaryW controlRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed controlUnary unaryK rationalRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed rationalUnary unaryQ realRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed unaryH unaryC localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row W ∨ hsame row K ∨
              hsame row Q ∨ hsame row E ∨ hsame row stepWindow ∨
                hsame row controlRead ∨ hsame row rationalRead ∨
                  hsame row realSeal ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R stepWindow ∧ Cont stepWindow W controlRead ∧
              Cont controlRead K rationalRead ∧ Cont rationalRead Q realSeal ∧
                Cont H C localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, stepRoute, controlRoute, rationalRoute, realRoute, localRoute,
          provenancePkg, localPkg⟩
  }
  exact ⟨cert, stepUnary, controlUnary, rationalUnary, realSealUnary, localUnary⟩

end BEDC.Derived.BarRecursionUp
