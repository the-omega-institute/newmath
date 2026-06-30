import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.EdelsteinFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EdelsteinFixedPointCarrier [AskSetup] [PackageSetup]
    (X K F O C S H R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧ UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory O ∧ UnaryHistory C ∧
    UnaryHistory S ∧ hsame H (append X K) ∧ Cont O K R ∧ Cont R S N ∧
      PkgSig bundle P pkg

theorem EdelsteinFixedPointCarrier_namecert_obligations
    [AskSetup] [PackageSetup] {X K F O C S H R P N fixedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EdelsteinFixedPointCarrier X K F O C S H R P N bundle pkg ->
      Cont O K fixedRead ->
        PkgSig bundle fixedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row fixedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row K ∨ hsame row F ∨ hsame row O ∨
                  hsame row C ∨ hsame row S ∨ hsame row fixedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont O K fixedRead ∧ PkgSig bundle fixedRead pkg)
              hsame ∧
            UnaryHistory fixedRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig UnaryHistory
  intro packet fixedRoute fixedPkg
  obtain ⟨_unaryX, unaryK, _unaryF, unaryO, _unaryC, _unaryS, _sameH, _routeR,
      _routeN, pkgP⟩ := packet
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed unaryO unaryK fixedRoute
  have sourceAtFixed : hsame fixedRead fixedRead ∧ UnaryHistory fixedRead :=
    ⟨hsame_refl fixedRead, fixedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fixedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K ∨ hsame row F ∨ hsame row O ∨
              hsame row C ∨ hsame row S ∨ hsame row fixedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O K fixedRead ∧ PkgSig bundle fixedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fixedRead sourceAtFixed
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, fixedRoute, fixedPkg⟩
  }
  exact ⟨cert, fixedUnary, pkgP⟩

end BEDC.Derived.EdelsteinFixedPointUp
