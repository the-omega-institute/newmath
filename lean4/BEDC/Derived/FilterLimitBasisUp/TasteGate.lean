import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

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

inductive FilterLimitBasisUp : Type where
  | mk (Q F L W R D E H C P N : BHist) : FilterLimitBasisUp
  deriving DecidableEq

def filterLimitBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterLimitBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterLimitBasisEncodeBHist h

def filterLimitBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterLimitBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterLimitBasisDecodeBHist tail)

private theorem filterLimitBasisDecode_encode_bhist :
    ∀ h : BHist, filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterLimitBasisFields : FilterLimitBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterLimitBasisUp.mk Q F L W R D E H C P N => [Q, F, L, W, R, D, E, H, C, P, N]

def filterLimitBasisToEventFlow : FilterLimitBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterLimitBasisFields x).map filterLimitBasisEncodeBHist

private def filterLimitBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterLimitBasisEventAtDefault index rest

def filterLimitBasisFromEventFlow (ef : EventFlow) : Option FilterLimitBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterLimitBasisUp.mk
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 0 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 1 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 2 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 3 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 4 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 5 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 6 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 7 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 8 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 9 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 10 ef)))

private theorem filterLimitBasis_round_trip :
    ∀ x : FilterLimitBasisUp,
      filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q F L W R D E H C P N =>
      change
        some
          (FilterLimitBasisUp.mk
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist Q))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist F))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist L))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist W))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist R))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist D))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist E))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist H))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist C))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist P))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist N))) =
          some (FilterLimitBasisUp.mk Q F L W R D E H C P N)
      rw [filterLimitBasisDecode_encode_bhist Q, filterLimitBasisDecode_encode_bhist F,
        filterLimitBasisDecode_encode_bhist L, filterLimitBasisDecode_encode_bhist W,
        filterLimitBasisDecode_encode_bhist R, filterLimitBasisDecode_encode_bhist D,
        filterLimitBasisDecode_encode_bhist E, filterLimitBasisDecode_encode_bhist H,
        filterLimitBasisDecode_encode_bhist C, filterLimitBasisDecode_encode_bhist P,
        filterLimitBasisDecode_encode_bhist N]

private theorem filterLimitBasisToEventFlow_injective {x y : FilterLimitBasisUp} :
    filterLimitBasisToEventFlow x = filterLimitBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) =
        filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow y) :=
    congrArg filterLimitBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (filterLimitBasis_round_trip x).symm
      (Eq.trans hread (filterLimitBasis_round_trip y)))

instance filterLimitBasisBHistCarrier : BHistCarrier FilterLimitBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterLimitBasisToEventFlow
  fromEventFlow := filterLimitBasisFromEventFlow

instance filterLimitBasisChapterTasteGate : ChapterTasteGate FilterLimitBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) = some x
    exact filterLimitBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (filterLimitBasisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FilterLimitBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterLimitBasisChapterTasteGate

theorem FilterLimitBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FilterLimitBasisUp) ∧
        Nonempty (ChapterTasteGate FilterLimitBasisUp) ∧
          filterLimitBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨filterLimitBasisDecode_encode_bhist,
      Nonempty.intro filterLimitBasisBHistCarrier,
      Nonempty.intro filterLimitBasisChapterTasteGate,
      rfl⟩

def FilterLimitBasisCarrier [AskSetup] [PackageSetup]
    (Q F L W R D E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame NameCert
  UnaryHistory Q ∧ UnaryHistory F ∧ UnaryHistory L ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ hsame H N ∧
        PkgSig bundle P pkg

theorem FilterLimitBasisNameCertObligations [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionBasis limitRoute realRoute localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q F completionBasis →
        Cont completionBasis L limitRoute →
          Cont limitRoute E realRoute →
            Cont H C localRead →
              PkgSig bundle P pkg →
                PkgSig bundle localRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                          hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row localRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont Q F completionBasis ∧
                          Cont completionBasis L limitRoute ∧ Cont limitRoute E realRoute ∧
                            Cont H C localRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle localRead pkg)
                      hsame ∧
                    UnaryHistory completionBasis ∧ UnaryHistory limitRoute ∧
                      UnaryHistory realRoute ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qf completionLimit limitReal hc pkgP pkgLocal
  obtain
    ⟨qUnary, fUnary, lUnary, _wUnary, _rUnary, _dUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionBasis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed completionUnary lUnary completionLimit
  have realUnary : UnaryHistory realRoute :=
    unary_cont_closed limitUnary eUnary limitReal
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceLocal :
      (fun row : BHist => hsame row localRead ∧ UnaryHistory row) localRead := by
    exact ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionBasis ∧
              Cont completionBasis L limitRoute ∧ Cont limitRoute E realRoute ∧
                Cont H C localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceLocal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qf, completionLimit, limitReal, hc, pkgP, pkgLocal⟩
  }
  exact ⟨cert, completionUnary, limitUnary, realUnary, localUnary⟩

end BEDC.Derived.FilterLimitBasisUp
