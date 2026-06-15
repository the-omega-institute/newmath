import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IsaacsEquationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IsaacsEquationCarrier [AskSetup] [PackageSetup]
    (game actionLeft actionRight value dyn pde ode realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory game ∧ UnaryHistory actionLeft ∧ UnaryHistory actionRight ∧
    UnaryHistory value ∧ UnaryHistory dyn ∧ UnaryHistory pde ∧ UnaryHistory ode ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ hsame transport game ∧
          Cont game actionLeft dyn ∧ Cont dyn actionRight value ∧ Cont value pde ode ∧
            Cont ode realSeal replay ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem IsaacsEquationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {game actionLeft actionRight value dyn pde ode realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsaacsEquationCarrier game actionLeft actionRight value dyn pde ode realSeal transport
        replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row game ∨ hsame row actionLeft ∨ hsame row actionRight ∨
              hsame row value ∨ hsame row dyn ∨ hsame row pde ∨ hsame row ode ∨
                hsame row realSeal ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory Cont
  intro carrier
  obtain ⟨unaryGame, _unaryActionLeft, _unaryActionRight, _unaryValue, _unaryDyn,
    _unaryPde, _unaryOde, _unaryRealSeal, _unaryTransport, _unaryReplay, _unaryProvenance,
    unaryLocalName, _transportSame, _gameActionDyn, _dynActionValue, _valuePdeOde,
    _odeRealReplay, provenancePkg, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row game ∨ hsame row actionLeft ∨ hsame row actionRight ∨
              hsame row value ∨ hsame row dyn ∨ hsame row pde ∨ hsame row ode ∨
                hsame row realSeal ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨hsame_refl localName, unaryLocalName⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }
  exact cert

end BEDC.Derived.IsaacsEquationUp
