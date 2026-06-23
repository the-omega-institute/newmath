import BEDC.Derived.ReflectionGapAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReflectionGapAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ReflectionGapAuditCarrier [AskSetup] [PackageSetup]
    (I G L Q F T R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory I ∧ UnaryHistory G ∧ UnaryHistory L ∧ UnaryHistory Q ∧
    UnaryHistory F ∧ UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont I G L ∧ Cont L Q F ∧ Cont F T R ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ReflectionGapAuditNonescape [AskSetup] [PackageSetup]
    {I G L Q F T R P N publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionGapAuditCarrier I G L Q F T R P N bundle pkg →
      Cont R N publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row G ∨ hsame row L ∨ hsame row Q ∨
                  hsame row F ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_iUnary, _gUnary, _lUnary, _qUnary, _fUnary, _tUnary, rUnary, _pUnary, nUnary,
    _inquiryGap, _ledgerContinuation, _finalizationTransport, _provenancePkg,
    namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary nUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row G ∨ hsame row L ∨ hsame row Q ∨ hsame row F ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact ⟨source.right, publicPkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ReflectionGapAuditUp
