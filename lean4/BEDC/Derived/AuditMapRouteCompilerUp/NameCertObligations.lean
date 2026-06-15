import BEDC.Derived.AuditMapRouteCompilerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapRouteCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapRouteCompilerNameCertObligations [AskSetup] [PackageSetup]
    {E S G A T C M F L H K P N routeRead evidenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory S →
        UnaryHistory G →
          UnaryHistory A →
            UnaryHistory T →
              UnaryHistory C →
                UnaryHistory M →
                  UnaryHistory F →
                    UnaryHistory L →
                      UnaryHistory H →
                        UnaryHistory K →
                          UnaryHistory P →
                            UnaryHistory N →
                              Cont E S routeRead →
                                Cont routeRead G evidenceRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                        (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row E ∨ hsame row S ∨ hsame row G ∨
                                            hsame row A ∨ hsame row T ∨ hsame row C ∨
                                              hsame row M ∨ hsame row F ∨ hsame row L ∨
                                                hsame row H ∨ hsame row K ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row routeRead ∨
                                                    hsame row evidenceRead)
                                        (fun row : BHist =>
                                          hsame row N ∧ Cont E S routeRead ∧
                                            Cont routeRead G evidenceRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _eUnary _sUnary _gUnary _aUnary _tUnary _cUnary _mUnary _fUnary _lUnary
    _hUnary _kUnary _pUnary nUnary routeCont evidenceCont provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeCont, evidenceCont, provenancePkg, namePkg⟩
  }

end BEDC.Derived.AuditMapRouteCompilerUp
