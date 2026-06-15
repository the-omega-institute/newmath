import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZeckendorfCarryClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZeckendorfCarryClassifierCarrier [AskSetup] [PackageSetup]
    (u v c s t h r p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory c ∧ UnaryHistory s ∧
    UnaryHistory t ∧ UnaryHistory p ∧ Cont u v c ∧ Cont c s r ∧ Cont r t h ∧
      Cont h p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg

theorem ZeckendorfCarryClassifierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {u v c s t h r p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryClassifierCarrier u v c s t h r p n bundle pkg ->
      UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory c ∧ UnaryHistory s ∧
        UnaryHistory t ∧ UnaryHistory h ∧ UnaryHistory r ∧ UnaryHistory p ∧
          UnaryHistory n ∧ Cont u v c ∧ Cont c s r ∧ PkgSig bundle n pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨uUnary, vUnary, cUnary, sUnary, tUnary, pUnary, uvCarry, carrySumRead,
    readTailHandoff, handoffProvenanceName, _provenancePkg, namePkg⟩ := carrier
  have rUnary : UnaryHistory r :=
    unary_cont_closed cUnary sUnary carrySumRead
  have hUnary : UnaryHistory h :=
    unary_cont_closed rUnary tUnary readTailHandoff
  have nUnary : UnaryHistory n :=
    unary_cont_closed hUnary pUnary handoffProvenanceName
  exact
    ⟨uUnary, vUnary, cUnary, sUnary, tUnary, hUnary, rUnary, pUnary, nUnary,
      uvCarry, carrySumRead, namePkg⟩

end BEDC.Derived.ZeckendorfCarryClassifierUp
