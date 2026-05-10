import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModelCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModelCatBHistSourcePacket [AskSetup] [PackageSetup]
    (category cof fib weak lift factor provenance rho lambda : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory cof ∧ UnaryHistory fib ∧ UnaryHistory weak ∧
    UnaryHistory provenance ∧ UnaryHistory rho ∧ Cont category cof lift ∧
      Cont fib weak factor ∧ Cont provenance factor lambda ∧ PkgSig bundle lambda pkg

theorem ModelCatBHistSourcePacket_root_obligation_surface [AskSetup] [PackageSetup]
    {category cof fib weak lift factor provenance rho lambda : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelCatBHistSourcePacket category cof fib weak lift factor provenance rho lambda bundle
        pkg ->
      UnaryHistory category ∧ UnaryHistory cof ∧ UnaryHistory fib ∧ UnaryHistory weak ∧
        UnaryHistory lift ∧ UnaryHistory factor ∧ UnaryHistory provenance ∧ UnaryHistory rho ∧
          UnaryHistory lambda ∧ Cont category cof lift ∧ Cont fib weak factor ∧
            Cont provenance factor lambda ∧ hsame lift (append category cof) ∧
              hsame factor (append fib weak) ∧ hsame lambda (append provenance factor) ∧
                PkgSig bundle lambda pkg := by
  intro packet
  obtain ⟨categoryUnary, cofUnary, fibUnary, weakUnary, provenanceUnary, rhoUnary,
    liftCont, factorCont, lambdaCont, pkgSig⟩ := packet
  have liftUnary : UnaryHistory lift :=
    unary_cont_closed categoryUnary cofUnary liftCont
  have factorUnary : UnaryHistory factor :=
    unary_cont_closed fibUnary weakUnary factorCont
  have lambdaUnary : UnaryHistory lambda :=
    unary_cont_closed provenanceUnary factorUnary lambdaCont
  exact
    ⟨categoryUnary, cofUnary, fibUnary, weakUnary, liftUnary, factorUnary, provenanceUnary,
      rhoUnary, lambdaUnary, liftCont, factorCont, lambdaCont, liftCont, factorCont,
      lambdaCont, pkgSig⟩

theorem ModelCatBHistSourcePacket_weak_equivalence_classifier_laws [AskSetup] [PackageSetup]
    {category cof fib weak lift factor provenance rho lambda : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelCatBHistSourcePacket category cof fib weak lift factor provenance rho lambda bundle
        pkg ->
      SemanticNameCert (fun row : BHist => hsame row weak)
          (fun row : BHist => hsame row weak) (fun row : BHist => hsame row weak)
          hsame ∧
        UnaryHistory weak ∧ PkgSig bundle lambda pkg := by
  intro packet
  obtain ⟨_categoryUnary, _cofUnary, _fibUnary, weakUnary, _provenanceUnary, _rhoUnary,
    _liftCont, _factorCont, _lambdaCont, pkgSig⟩ := packet
  have cert :
      SemanticNameCert (fun row : BHist => hsame row weak)
          (fun row : BHist => hsame row weak) (fun row : BHist => hsame row weak)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro weak (hsame_refl weak)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, weakUnary, pkgSig⟩

end BEDC.Derived.ModelCatUp
