import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_real_seal_uniqueness_boundary [AskSetup] [PackageSetup]
    {W M Q T S H C P N firstSeal secondSeal sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont T S firstSeal ->
        Cont T S secondSeal ->
          Cont W M sharedRead ->
            PkgSig bundle P pkg ->
              hsame firstSeal secondSeal ∧ UnaryHistory firstSeal ∧
                UnaryHistory secondSeal ∧ UnaryHistory sharedRead ∧ Cont W M sharedRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier firstSealRoute secondSealRoute sharedRoute _pkgSig
  obtain ⟨wUnary, mUnary, _qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _carrierWMQ, _carrierMQT, _carrierTS, _carrierCN, _carrierPkg⟩ := carrier
  have firstSealUnary : UnaryHistory firstSeal :=
    unary_cont_closed tUnary sUnary firstSealRoute
  have secondSealUnary : UnaryHistory secondSeal :=
    unary_cont_closed tUnary sUnary secondSealRoute
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed wUnary mUnary sharedRoute
  have sameSeal : hsame firstSeal secondSeal :=
    cont_respects_hsame (hsame_refl T) (hsame_refl S) firstSealRoute secondSealRoute
  exact ⟨sameSeal, firstSealUnary, secondSealUnary, sharedUnary, sharedRoute⟩

end BEDC.Derived.CauchyOscillationUp
