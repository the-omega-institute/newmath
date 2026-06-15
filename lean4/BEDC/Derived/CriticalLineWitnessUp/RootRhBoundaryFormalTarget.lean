import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_criticallinewitness_root_rh_boundary_formal_target
    [AskSetup] [PackageSetup] {Z S M R Q H C P N rhRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rhRead ->
        PkgSig bundle P pkg ->
          PkgSig bundle rhRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row rhRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont (append Z S) Q rhRead ∧
                    PkgSig bundle rhRead pkg)
                hsame ∧
              UnaryHistory rhRead ∧ hsame H (append Z S) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig UnaryHistory
  intro packet rhRoute pkgP pkgRh
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed sourceUnary unaryQ rhRoute
  have sourceAtRh : hsame rhRead rhRead ∧ UnaryHistory rhRead :=
    ⟨hsame_refl rhRead, rhUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row rhRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont (append Z S) Q rhRead ∧ PkgSig bundle rhRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead sourceAtRh
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rhRoute, pkgRh⟩
  }
  exact ⟨cert, rhUnary, sameH, pkgP⟩

end BEDC.Derived.CriticalLineWitnessUp
