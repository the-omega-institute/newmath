import BEDC.Derived.UniformCompletionFunctorUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCompletionFunctorCarrier [AskSetup] [PackageSetup]
    (U F E R W D S H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory U ∧ UnaryHistory F ∧ UnaryHistory E ∧ UnaryHistory R ∧
    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont U F E ∧ Cont E R W ∧ Cont W D S ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem UniformCompletionFunctorCarrier_source_factorization [AskSetup] [PackageSetup]
    {U F E R W D S H C P N handoffRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F handoffRead ->
        Cont handoffRead E sealRead ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨
                  hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row handoffRead ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont U F handoffRead ∧
                  Cont handoffRead E sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory handoffRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier handoffRoute sealRoute
  obtain ⟨unaryU, unaryF, unaryE, _unaryR, _unaryW, _unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed unaryU unaryF handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row E ∨ hsame row R ∨ hsame row W ∨
              hsame row D ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row handoffRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F handoffRead ∧ Cont handoffRead E sealRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, handoffUnary, sealUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
