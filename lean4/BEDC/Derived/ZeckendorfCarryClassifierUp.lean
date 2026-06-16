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

theorem ZeckendorfCarryClassifierCarrier_window_determinacy [AskSetup] [PackageSetup]
    {u v c s t h r p n carriedWindow cSourceRead carriedSourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZeckendorfCarryClassifierCarrier u v c s t h r p n bundle pkg ->
      Cont u v carriedWindow ->
        Cont c s cSourceRead ->
          Cont carriedWindow s carriedSourceRead ->
            hsame c carriedWindow ∧ hsame cSourceRead carriedSourceRead ∧
              UnaryHistory carriedSourceRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier carriedWindowRoute cSourceRoute carriedSourceRoute
  obtain ⟨uUnary, vUnary, _cUnary, sUnary, _tUnary, _pUnary, uvCarry, _carrySumRead,
    _readTailHandoff, _handoffProvenanceName, _provenancePkg, _namePkg⟩ := carrier
  have sameCarryWindow : hsame c carriedWindow :=
    cont_deterministic uvCarry carriedWindowRoute
  have sameSourceRead : hsame cSourceRead carriedSourceRead :=
    cont_respects_hsame sameCarryWindow (hsame_refl s) cSourceRoute carriedSourceRoute
  have carriedWindowUnary : UnaryHistory carriedWindow :=
    unary_cont_closed uUnary vUnary carriedWindowRoute
  have carriedSourceUnary : UnaryHistory carriedSourceRead :=
    unary_cont_closed carriedWindowUnary sUnary carriedSourceRoute
  exact ⟨sameCarryWindow, sameSourceRead, carriedSourceUnary⟩

end BEDC.Derived.ZeckendorfCarryClassifierUp
