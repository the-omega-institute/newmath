import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealZeroUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealZeroUp : Type where
  | mk (q S Z0 D R H C P N : BHist) : RealZeroUp

def RealZeroCarrier (q S Z0 D R H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame NameCert
  UnaryHistory q ∧ UnaryHistory S ∧ UnaryHistory Z0 ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont q S Z0 ∧ Cont Z0 D R ∧ hsame H H ∧
        hsame C C ∧ hsame P P ∧ hsame N N ∧
          Nonempty (NameCert (fun row : BHist => hsame row R) hsame)

private def RealZeroCarrier_terminal_core (R : BHist) :
    NameCert (fun row : BHist => hsame row R) hsame where
  -- BEDC touchpoint anchor: BHist hsame NameCert
  carrier_inhabited := Exists.intro R (hsame_refl R)
  equiv_refl := by
    intro row _source
    exact hsame_refl row
  equiv_symm := by
    intro _row _other same
    exact hsame_symm same
  equiv_trans := by
    intro _row _other _third sameRO sameOT
    exact hsame_trans sameRO sameOT
  carrier_respects_equiv := by
    intro _row _other same source
    exact hsame_trans (hsame_symm same) source

theorem RealZeroCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q S Z0 D R H C P N namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealZeroCarrier q S Z0 D R H C P N ->
      Cont R N namedRead ->
        PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
                    hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont q S Z0 ∧ Cont Z0 D R ∧
                    Cont R N namedRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RealZeroCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier namedRoute pkgP pkgN
  obtain ⟨_qUnary, _sUnary, _z0Unary, _dUnary, rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, zeroRoute, terminalRoute, _sameH, _sameC, _sameP, _sameN,
    _terminalCert⟩ := carrier
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed rUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S Z0 ∧ Cont Z0 D R ∧ Cont R N namedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zeroRoute, terminalRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, namedUnary⟩

theorem RealZeroCarrier_terminal_seal_handoff {q S Z0 D R H C P N : BHist} :
    RealZeroCarrier q S Z0 D R H C P N ->
      SemanticNameCert
          (fun row : BHist => hsame row R)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row R ∧ Cont q S Z0 ∧ Cont Z0 D R)
          hsame ∧
        Cont q S Z0 ∧ Cont Z0 D R := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro carrier
  obtain ⟨_qUnary, _sUnary, _z0Unary, _dUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, qToS, zToD, _sameH, _sameC, _sameP, _sameN, _terminalCert⟩ := carrier
  constructor
  · exact {
      core := RealZeroCarrier_terminal_core R
      pattern_sound := by
        intro _row source
        right
        right
        right
        right
        exact Or.inl source
      ledger_sound := by
        intro _row source
        exact ⟨source, qToS, zToD⟩
    }
  · exact ⟨qToS, zToD⟩

theorem RealZeroCarrier_stationary_source_obligation {q S Z0 D R H C P N : BHist} :
    RealZeroCarrier q S Z0 D R H C P N ->
      Nonempty (NameCert (fun row : BHist => hsame row Z0) hsame) ∧
        Cont q S Z0 ∧ hsame H H := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  intro carrier
  obtain ⟨_qUnary, _sUnary, _z0Unary, _dUnary, _rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, qToS, _zToD, sameH, _sameC, _sameP, _sameN, _terminalCert⟩ := carrier
  constructor
  · exact
      Nonempty.intro {
        carrier_inhabited := Exists.intro Z0 (hsame_refl Z0)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _other _third sameRO sameOT
          exact hsame_trans sameRO sameOT
        carrier_respects_equiv := by
          intro _row _other same source
          exact hsame_trans (hsame_symm same) source
      }
  · exact ⟨qToS, sameH⟩

theorem RealZeroCarrier_downstream_consumer_obligation [AskSetup] [PackageSetup]
    {q S Z0 D R H C P N namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealZeroCarrier q S Z0 D R H C P N ->
      Cont R N namedRead ->
        PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
                      hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont q S Z0 ∧ Cont Z0 D R ∧
                      Cont R N namedRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory namedRead ∧ Cont q S Z0 ∧ Cont Z0 D R := by
  -- BEDC touchpoint anchor: RealZeroCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier namedRoute pkgP pkgN pkgNamed
  obtain ⟨_qUnary, _sUnary, _z0Unary, _dUnary, rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, zeroRoute, terminalRoute, _sameH, _sameC, _sameP, _sameN,
    _terminalCert⟩ := carrier
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed rUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S Z0 ∧ Cont Z0 D R ∧ Cont R N namedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, zeroRoute, terminalRoute, namedRoute, pkgP, pkgN, pkgNamed⟩
  }
  exact ⟨cert, namedUnary, zeroRoute, terminalRoute⟩

end BEDC.Derived.RealZeroUp
