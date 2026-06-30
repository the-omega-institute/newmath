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
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory q ∧ UnaryHistory S ∧ UnaryHistory Z0 ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont q S Z0 ∧ Cont Z0 D R

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
  obtain ⟨_qUnary, _sUnary, z0Unary, dUnary, rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, zeroRoute, terminalRoute⟩ := carrier
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

end BEDC.Derived.RealZeroUp
