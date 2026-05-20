import BEDC.Derived.CauchyWindowTransducerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyWindowTransducerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyWindowTransducerCarrier [AskSetup] [PackageSetup]
    (S D W R E L H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S D W ∧ Cont W R E ∧ hsame N E

theorem CauchyWindowTransducerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S D W R E L H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyWindowTransducerCarrier S D W R E L H C P N →
      PkgSig bundle E pkg →
        UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧
          UnaryHistory E ∧ UnaryHistory L ∧ Cont S D W ∧ Cont W R E ∧
            hsame N E ∧ PkgSig bundle E pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row E ∧ UnaryHistory row)
                (fun row : BHist => hsame row E ∧ Cont S D W ∧ Cont W R E)
                (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier pkgE
  obtain ⟨unaryS, unaryD, unaryW, unaryR, unaryE, unaryL, _unaryH, _unaryC,
    _unaryP, _unaryN, contSDW, contWRE, sameNE⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row E ∧ UnaryHistory row)
        (fun row : BHist => hsame row E ∧ Cont S D W ∧ Cont W R E)
        (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨hsame_refl E, unaryE⟩
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
        intro row other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, contSDW, contWRE⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgE⟩
  }
  exact ⟨unaryS, unaryD, unaryW, unaryR, unaryE, unaryL, contSDW, contWRE, sameNE,
    pkgE, cert⟩

theorem CauchyWindowTransducerCarrier_step_spine_determinacy [AskSetup] [PackageSetup]
    {S D W R E L H C P N : BHist} :
    CauchyWindowTransducerCarrier S D W R E L H C P N →
      UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
        Cont S D W ∧ Cont W R E ∧ hsame N E := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier
  obtain ⟨_unaryS, _unaryD, unaryW, unaryR, unaryE, _unaryL, _unaryH, _unaryC,
    _unaryP, _unaryN, contSDW, contWRE, sameNE⟩ := carrier
  exact ⟨unaryW, unaryR, unaryE, contSDW, contWRE, sameNE⟩

end BEDC.Derived.CauchyWindowTransducerUp
