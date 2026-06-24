import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CoveringHomotopyLiftingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringHomotopyLiftingCarrier [AskSetup] [PackageSetup]
    (F pi f0 I U W Sigma E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory F ∧ UnaryHistory pi ∧ UnaryHistory f0 ∧ UnaryHistory I ∧
    UnaryHistory U ∧ UnaryHistory W ∧ UnaryHistory Sigma ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CoveringHomotopyLiftingNameCert_obligations [AskSetup] [PackageSetup]
    {F pi f0 I U W Sigma E H C P N liftRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringHomotopyLiftingCarrier F pi f0 I U W Sigma E H C P N bundle pkg →
      Cont C N liftRead →
        PkgSig bundle liftRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row liftRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row F ∨ hsame row pi ∨ hsame row f0 ∨ hsame row I ∨
                  hsame row U ∨ hsame row W ∨ hsame row Sigma ∨ hsame row E ∨
                    hsame row liftRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N liftRead ∧ PkgSig bundle liftRead pkg)
              hsame ∧
            UnaryHistory liftRead := by
  -- BEDC touchpoint anchor: CoveringHomotopyLiftingCarrier BHist Cont PkgSig hsame SemanticNameCert
  intro carrier replayRoute liftPkg
  obtain ⟨_fUnary, _piUnary, _f0Unary, _iUnary, _uUnary, _wUnary, _sigmaUnary,
    _eUnary, _hUnary, cUnary, _pUnary, nUnary, _provenancePkg, _namePkg⟩ := carrier
  have liftUnary : UnaryHistory liftRead :=
    unary_cont_closed cUnary nUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row liftRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row pi ∨ hsame row f0 ∨ hsame row I ∨
              hsame row U ∨ hsame row W ∨ hsame row Sigma ∨ hsame row E ∨
                hsame row liftRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N liftRead ∧ PkgSig bundle liftRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro liftRead ⟨hsame_refl liftRead, liftUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, liftPkg⟩
  }
  exact ⟨cert, liftUnary⟩

end BEDC.Derived.CoveringHomotopyLiftingUp
