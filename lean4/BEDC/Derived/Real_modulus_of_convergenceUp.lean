import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.Real_modulus_of_convergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealModulusOfConvergenceCarrier [AskSetup] [PackageSetup]
    (D W Q M E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: RealModulusOfConvergenceCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory M ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont D W Q ∧ Cont Q M E ∧ Cont E H C ∧ PkgSig bundle P pkg

theorem RealModulusOfConvergenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D W Q M E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusOfConvergenceCarrier D W Q M E H C P N bundle pkg →
      Cont M E sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                  hsame row E ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W Q ∧ Cont Q M E ∧ Cont M E sealRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
              hsame ∧
            UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory M ∧
              UnaryHistory E ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealModulusOfConvergenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier modulusSeal sealPkg
  obtain ⟨dUnary, wUnary, qUnary, mUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    dWindowReadback, readbackModulusSeal, _sealTransportReplay, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed mUnary eUnary modulusSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W Q ∧ Cont Q M E ∧ Cont M E sealRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dWindowReadback, readbackModulusSeal, modulusSeal,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, dUnary, wUnary, qUnary, mUnary, eUnary, sealUnary⟩

end BEDC.Derived.Real_modulus_of_convergenceUp
