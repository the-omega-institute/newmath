import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyNetCompletionCarrier [AskSetup] [PackageSetup]
    (D W Q M U S R A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory M ∧
    UnaryHistory U ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory A ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont D W Q ∧ Cont Q M U ∧ Cont U S R ∧ Cont R A H ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyNetCompletionCarrier_moore_smith_handoff [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead M handoffRead ->
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                  hsame row U ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row boundaryRead ∨ hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W boundaryRead ∧
                  Cont boundaryRead M handoffRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory boundaryRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute handoffRoute
  obtain ⟨unaryD, unaryW, _unaryQ, unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundaryUnary unaryM handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row boundaryRead ∨
                  hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧
              Cont boundaryRead M handoffRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, handoffRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, handoffUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
