import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteStreamCarrier [AskSetup] [PackageSetup]
    (Q L W R D H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory Q ∧ UnaryHistory L ∧ Cont Q L W ∧ UnaryHistory W ∧ UnaryHistory R ∧
    Cont W R D ∧ UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧
      PkgSig bundle P pkg ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem FiniteStreamCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q L W R D H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteStreamCarrier Q L W R D H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q L W ∧ Cont W R D ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory W ∧ UnaryHistory D := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro carrier
  obtain
    ⟨unaryQ, unaryL, contQLW, unaryW, unaryR, contWRD, unaryD, _unaryH, _unaryC,
      pkgP, unaryN, pkgN⟩ := carrier
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N :=
    ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q L W ∧ Cont W R D ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameNext
        exact hsame_trans sameRow sameNext
      carrier_respects_equiv := by
        intro row row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro row source
      cases source.left
      exact ⟨unaryN, contQLW, contWRD, pkgP, pkgN⟩
  }
  exact ⟨cert, unaryW, unaryD⟩

end BEDC.Derived.FiniteStreamUp
