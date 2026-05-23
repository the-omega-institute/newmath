import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyIntervalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyIntervalSelectorCarrier (D S R J E H C _P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory J ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ Cont D S R ∧ Cont R J E ∧ hsame N E

theorem RegularCauchyIntervalSelectorCarrier_nesting_extraction
    [AskSetup] [PackageSetup]
    {D S R J E H C P N sealRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyIntervalSelectorCarrier D S R J E H C P N →
      Cont D S R →
        Cont R J sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory J ∧
              UnaryHistory sealRead ∧ Cont D S R ∧ Cont R J sealRead ∧
                PkgSig bundle sealRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row sealRead ∧ Cont D S R ∧
                      Cont R J sealRead)
                    (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier selectedRoute nestingRoute sealPkg
  obtain ⟨unaryD, unaryS, unaryJ, _unaryE, _unaryH, _unaryC, _carrierRoute,
    _sealRoute, _sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryS selectedRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryR unaryJ nestingRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row sealRead ∧ Cont D S R ∧ Cont R J sealRead)
        (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨hsame_refl sealRead, unarySeal⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, selectedRoute, nestingRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, sealPkg⟩
    }
  exact
    ⟨unaryD, unaryS, unaryR, unaryJ, unarySeal, selectedRoute, nestingRoute, sealPkg,
      cert⟩

theorem RegularCauchyIntervalSelectorCarrier_real_seal_handoff
    [AskSetup] [PackageSetup]
    {D S R J E H C P N sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyIntervalSelectorCarrier D S R J E H C P N →
      Cont D S R →
        Cont R J sealRead →
          Cont sealRead E publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory J ∧
                UnaryHistory sealRead ∧ UnaryHistory publicRead ∧ Cont D S R ∧
                  Cont R J sealRead ∧ Cont sealRead E publicRead ∧
                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier selectedRoute nestingRoute sealRoute publicPkg
  obtain ⟨unaryD, unaryS, unaryJ, unaryE, _unaryH, _unaryC, _carrierRoute,
    _sealCarrierRoute, _sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryS selectedRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryR unaryJ nestingRoute
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unarySeal unaryE sealRoute
  exact
    ⟨unaryD, unaryS, unaryR, unaryJ, unarySeal, unaryPublic, selectedRoute, nestingRoute,
      sealRoute, publicPkg⟩

theorem RegularCauchyIntervalSelectorCarrier_schedule_exposure
    [AskSetup] [PackageSetup]
    {D S R J E H C P N scheduleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyIntervalSelectorCarrier D S R J E H C P N →
      Cont D S scheduleRead →
        PkgSig bundle scheduleRead pkg →
          UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory scheduleRead ∧
            Cont D S scheduleRead ∧ UnaryHistory H ∧ UnaryHistory C ∧ hsame N E ∧
              PkgSig bundle scheduleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier scheduleRoute schedulePkg
  obtain ⟨unaryD, unaryS, _unaryJ, _unaryE, unaryH, unaryC, _carrierRoute,
    _sealRoute, sameNameSeal⟩ := carrier
  have unarySchedule : UnaryHistory scheduleRead :=
    unary_cont_closed unaryD unaryS scheduleRoute
  exact
    ⟨unaryD, unaryS, unarySchedule, scheduleRoute, unaryH, unaryC, sameNameSeal,
      schedulePkg⟩

end BEDC.Derived.RegularCauchyIntervalSelectorUp
