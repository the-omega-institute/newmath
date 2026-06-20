import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNonzeroUp

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

inductive RegularCauchyNonzeroUp : Type where
  | mk (Q A W D R E H C P N : BHist) : RegularCauchyNonzeroUp
  deriving DecidableEq

def regularCauchyNonzeroEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNonzeroEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNonzeroEncodeBHist h

def regularCauchyNonzeroDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNonzeroDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNonzeroDecodeBHist tail)

private theorem regularCauchyNonzero_decode_encode :
    ∀ h : BHist, regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyNonzeroFields : RegularCauchyNonzeroUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNonzeroUp.mk Q A W D R E H C P N => [Q, A, W, D, R, E, H, C, P, N]

def regularCauchyNonzeroToEventFlow : RegularCauchyNonzeroUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyNonzeroFields x).map regularCauchyNonzeroEncodeBHist

private def regularCauchyNonzeroEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyNonzeroEventAtDefault index rest

def regularCauchyNonzeroFromEventFlow (ef : EventFlow) : Option RegularCauchyNonzeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyNonzeroUp.mk
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 0 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 1 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 2 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 3 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 4 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 5 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 6 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 7 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 8 ef))
      (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 9 ef)))

private theorem regularCauchyNonzero_round_trip :
    ∀ x : RegularCauchyNonzeroUp,
      regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A W D R E H C P N =>
      change
        some
          (RegularCauchyNonzeroUp.mk
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist Q))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist A))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist W))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist D))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist R))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist E))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist H))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist C))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist P))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist N))) =
          some (RegularCauchyNonzeroUp.mk Q A W D R E H C P N)
      rw [regularCauchyNonzero_decode_encode Q, regularCauchyNonzero_decode_encode A,
        regularCauchyNonzero_decode_encode W, regularCauchyNonzero_decode_encode D,
        regularCauchyNonzero_decode_encode R, regularCauchyNonzero_decode_encode E,
        regularCauchyNonzero_decode_encode H, regularCauchyNonzero_decode_encode C,
        regularCauchyNonzero_decode_encode P, regularCauchyNonzero_decode_encode N]

private theorem regularCauchyNonzero_toEventFlow_injective {x y : RegularCauchyNonzeroUp} :
    regularCauchyNonzeroToEventFlow x = regularCauchyNonzeroToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) =
        regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow y) :=
    congrArg regularCauchyNonzeroFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyNonzero_round_trip x).symm
      (Eq.trans hread (regularCauchyNonzero_round_trip y)))

instance regularCauchyNonzeroBHistCarrier : BHistCarrier RegularCauchyNonzeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNonzeroToEventFlow
  fromEventFlow := regularCauchyNonzeroFromEventFlow

instance regularCauchyNonzeroChapterTasteGate : ChapterTasteGate RegularCauchyNonzeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) = some x
    exact regularCauchyNonzero_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNonzero_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyNonzeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyNonzeroChapterTasteGate

def RegularCauchyNonzeroCarrier [AskSetup] [PackageSetup]
    (Q A W D R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory Q ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem RegularCauchyNonzeroNamecertObligations [AskSetup] [PackageSetup]
    {Q A W D R E H C P N sourceRead apartnessRead windowRead lowerBoundRead handoffRead
      realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNonzeroCarrier Q A W D R E H C P N bundle pkg ->
      Cont Q A sourceRead ->
        Cont sourceRead W apartnessRead ->
          Cont apartnessRead D windowRead ->
            Cont windowRead R handoffRead ->
              Cont handoffRead E realRead ->
                Cont realRead N namedRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row Q ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨
                          hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont Q A sourceRead ∧
                          Cont sourceRead W apartnessRead ∧
                            Cont apartnessRead D windowRead ∧
                              Cont windowRead R handoffRead ∧
                                Cont handoffRead E realRead ∧
                                  Cont realRead N namedRead ∧ PkgSig bundle P pkg)
                      hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute apartnessRoute windowRoute handoffRoute realRoute namedRoute
  obtain ⟨qUnary, aUnary, wUnary, dUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed qUnary aUnary sourceRoute
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed sourceUnary wUnary apartnessRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed apartnessUnary dUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary rUnary handoffRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed handoffUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q A sourceRead ∧ Cont sourceRead W apartnessRead ∧
              Cont apartnessRead D windowRead ∧ Cont windowRead R handoffRead ∧
                Cont handoffRead E realRead ∧ Cont realRead N namedRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, apartnessRoute, windowRoute, handoffRoute, realRoute,
          namedRoute, provenancePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.RegularCauchyNonzeroUp
