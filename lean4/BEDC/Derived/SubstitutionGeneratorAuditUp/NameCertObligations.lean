import BEDC.Derived.SubstitutionGeneratorAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubstitutionGeneratorAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubstitutionGeneratorAuditCarrier [AskSetup] [PackageSetup]
    (T C R S K W H Q P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory R ∧ UnaryHistory S ∧
    UnaryHistory K ∧ UnaryHistory W ∧ UnaryHistory H ∧ UnaryHistory Q ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont W Q N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem SubstitutionGeneratorAuditCarrier_namecert_projection [AskSetup] [PackageSetup]
    {T C R S K W H Q P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionGeneratorAuditCarrier T C R S K W H Q P N bundle pkg →
      UnaryHistory N ∧ Cont W Q N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: SubstitutionGeneratorAuditCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨_tUnary, _cUnary, _rUnary, _sUnary, _kUnary, _wUnary, _hUnary, _qUnary,
    _pUnary, nUnary, nameRoute, provenancePkg, namePkg⟩ := carrier
  exact ⟨nUnary, nameRoute, provenancePkg, namePkg⟩

theorem SubstitutionGeneratorAuditCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T C R S K W H Q P N nameRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (nameUnary : UnaryHistory N) (replayUnary : UnaryHistory W)
    (continuationUnary : UnaryHistory Q) (nameRoute : Cont W Q nameRead)
    (namePkg : PkgSig bundle N pkg) :
    SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row T ∨ hsame row C ∨ hsame row R ∨ hsame row S ∨ hsame row K ∨
            hsame row W ∨ hsame row H ∨ hsame row Q ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => UnaryHistory row ∧ Cont W Q nameRead ∧ PkgSig bundle N pkg)
        hsame ∧
      UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed replayUnary continuationUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row C ∨ hsame row R ∨ hsame row S ∨ hsame row K ∨
              hsame row W ∨ hsame row H ∨ hsame row Q ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont W Q nameRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nameUnary⟩
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
                      (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nameRoute, namePkg⟩
  }
  exact ⟨cert, nameReadUnary⟩

end BEDC.Derived.SubstitutionGeneratorAuditUp
