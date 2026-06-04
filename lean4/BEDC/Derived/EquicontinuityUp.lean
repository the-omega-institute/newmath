import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EquicontinuityCarrier [AskSetup] [PackageSetup]
    (K F eps rho M T R P N radiusRead handoffRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧ UnaryHistory R ∧
    UnaryHistory N ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EquicontinuityCarrier_shared_radius_stability [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
        Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, compactFamily, radiusHandoff,
    pkgP, pkgN⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho radiusHandoff
  exact ⟨radiusUnary, handoffUnary, compactFamily, radiusHandoff, pkgP, pkgN⟩

theorem EquicontinuityCarrier_compact_net_radius_exactness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont handoffRead M compactNetRead ->
          PkgSig bundle compactNetRead pkg ->
            UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
              UnaryHistory compactNetRead ∧ Cont K F radiusRead ∧
                Cont radiusRead rho handoffRead ∧ Cont handoffRead M compactNetRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle compactNetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier unaryM compactNetCont compactNetPkg
  obtain ⟨radiusUnary, handoffUnary, radiusCont, handoffCont, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed handoffUnary unaryM compactNetCont
  exact
    ⟨radiusUnary, handoffUnary, compactNetUnary, radiusCont, handoffCont, compactNetCont,
      pkgP, compactNetPkg⟩

theorem EquicontinuityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont K F radiusRead ->
      Cont radiusRead rho handoffRead ->
        PkgSig bundle P pkg ->
          UnaryHistory K ->
            UnaryHistory F ->
              UnaryHistory rho ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                        hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                          hsame row N ∨ hsame row radiusRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K F radiusRead ∧
                        Cont radiusRead rho handoffRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory radiusRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro compactFamily radiusHandoff pkgP unaryK unaryF unaryRho
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho radiusHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row radiusRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                      (Or.inr
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactFamily, radiusHandoff, pkgP⟩
  }
  exact ⟨cert, radiusUnary, handoffUnary⟩

theorem EquicontinuityCompactMetricRoute [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont K F compactRead ->
        Cont compactRead rho handoffRead ->
          UnaryHistory compactRead ∧ UnaryHistory handoffRead ∧
            Cont K F compactRead ∧ Cont compactRead rho handoffRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier compactRoute handoffRoute
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, _radiusRoute, _radiusHandoff,
    pkgP, pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed compactUnary unaryRho handoffRoute
  exact ⟨compactUnary, handoffUnary, compactRoute, handoffRoute, pkgP, pkgN⟩

theorem EquicontinuityCarrier_uniform_modulus_handoff [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho uniformRead ->
          Cont uniformRead M handoffRead ->
          UnaryHistory uniformRead ∧ UnaryHistory handoffRead ∧
            Cont K F radiusRead ∧ Cont radiusRead rho uniformRead ∧
              Cont uniformRead M handoffRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier unaryM radiusUniform uniformHandoff
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, compactFamily, _radiusHandoff,
    pkgP, pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed radiusUnary unaryRho radiusUniform
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed uniformUnary unaryM uniformHandoff
  exact
    ⟨uniformUnary, handoffUnary, compactFamily, radiusUniform, uniformHandoff, pkgP, pkgN⟩

theorem EquicontinuityCarrier_shared_radius_obligation [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho sharedRead ->
          Cont sharedRead M handoffRead ->
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                    hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                      hsame row N ∨ hsame row sharedRead ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F radiusRead ∧
                    Cont radiusRead rho sharedRead ∧ Cont sharedRead M handoffRead ∧
                      PkgSig bundle P pkg)
                hsame ∧ UnaryHistory sharedRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM radiusShared sharedHandoff
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, compactFamily, _radiusHandoff,
    pkgP, _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed radiusUnary unaryRho radiusShared
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sharedUnary unaryM sharedHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row sharedRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho sharedRead ∧
              Cont sharedRead M handoffRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                      (Or.inr
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactFamily, radiusShared, sharedHandoff, pkgP⟩
  }
  exact ⟨cert, sharedUnary, handoffUnary⟩

theorem EquicontinuityFamilyWindowExposure [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont handoffRead R consumerRead ->
        Cont K (append F (append rho R)) consumerRead ∧
          UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧ UnaryHistory consumerRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier consumerRoute
  obtain ⟨unaryK, unaryF, unaryRho, unaryR, _unaryN, radiusRoute, handoffRoute, pkgP,
    pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho handoffRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed handoffUnary unaryR consumerRoute
  have windowRoute : Cont K (append F (append rho R)) consumerRead := by
    cases radiusRoute
    cases handoffRoute
    cases consumerRoute
    exact
      (append_assoc (append K F) rho R).trans
        (append_assoc K F (append rho R))
  exact ⟨windowRoute, radiusUnary, handoffUnary, consumerUnary, pkgP, pkgN⟩

theorem EquicontinuityUniformModulusHandoff [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont handoffRead M uniformRead ->
          PkgSig bundle uniformRead pkg ->
            UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
              UnaryHistory uniformRead ∧ Cont K F radiusRead ∧
                Cont radiusRead rho handoffRead ∧ Cont handoffRead M uniformRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM handoffUniform uniformPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed handoffUnary unaryM handoffUniform
  exact
    ⟨radiusUnary, handoffUnary, uniformUnary, radiusRoute, handoffRoute, handoffUniform,
      pkgP, uniformPkg⟩

theorem EquicontinuityCarrier_transport_replay_provenance [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      Cont handoffRead R consumerRead →
        PkgSig bundle consumerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                  hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                    hsame row handoffRead ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont handoffRead R consumerRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg)
              hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨unaryK, unaryF, unaryRho, unaryR, _unaryN, radiusRoute, handoffRoute, pkgP,
    _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho handoffRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed handoffUnary unaryR consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row handoffRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoffRead R consumerRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerRoute, pkgP, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

theorem EquicontinuitySharedRadiusFamilyNonescape [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyRead coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho familyRead ->
          Cont familyRead M coverRead ->
            PkgSig bundle coverRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row radiusRead ∨
                      hsame row familyRead ∨ hsame row coverRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K F radiusRead ∧
                      Cont radiusRead rho familyRead ∧ Cont familyRead M coverRead ∧
                        PkgSig bundle coverRead pkg)
                  hsame ∧
                UnaryHistory familyRead ∧ UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM radiusFamily familyCover coverPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, radiusRoute, _handoffRoute,
    _pkgP, _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed radiusUnary unaryRho radiusFamily
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed familyUnary unaryM familyCover
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row radiusRead ∨
              hsame row familyRead ∨ hsame row coverRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho familyRead ∧
              Cont familyRead M coverRead ∧ PkgSig bundle coverRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverRead ⟨hsame_refl coverRead, coverUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, radiusRoute, radiusFamily, familyCover, coverPkg⟩
  }
  exact ⟨cert, familyUnary, coverUnary⟩

theorem EquicontinuitySharedRadiusStability [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory T ->
        Cont rho T transportedRead ->
          PkgSig bundle transportedRead pkg ->
            UnaryHistory rho ∧ UnaryHistory T ∧ UnaryHistory transportedRead ∧
              Cont rho T transportedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryT transportRoute transportPkg
  obtain ⟨_unaryK, _unaryF, unaryRho, _unaryR, _unaryN, _radiusRoute, _handoffRoute,
    pkgP, _pkgN⟩ := carrier
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed unaryRho unaryT transportRoute
  exact ⟨unaryRho, unaryT, transportedUnary, transportRoute, pkgP, transportPkg⟩

theorem EquicontinuityCarrier_family_modulus_consumer_exhaustion [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho familyRead ->
          Cont familyRead M handoffRead ->
            Cont handoffRead R consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory radiusRead ∧ UnaryHistory familyRead ∧
                  UnaryHistory handoffRead ∧ UnaryHistory consumerRead ∧
                    Cont K F radiusRead ∧ Cont radiusRead rho familyRead ∧
                      Cont familyRead M handoffRead ∧ Cont handoffRead R consumerRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier mUnary radiusFamily familyHandoff handoffConsumer consumerPkg
  obtain ⟨kUnary, fUnary, rhoUnary, rUnary, _unaryN, radiusRoute, _radiusHandoff,
    pkgP, _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed kUnary fUnary radiusRoute
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed radiusUnary rhoUnary radiusFamily
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed familyUnary mUnary familyHandoff
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed handoffUnary rUnary handoffConsumer
  exact
    ⟨radiusUnary, familyUnary, handoffUnary, consumerUnary, radiusRoute, radiusFamily,
      familyHandoff, handoffConsumer, pkgP, consumerPkg⟩

theorem EquicontinuityFiniteNetSelectorReadiness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead selectorRead readyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M -> Cont radiusRead rho selectorRead ->
        Cont selectorRead M readyRead -> PkgSig bundle readyRead pkg ->
          SemanticNameCert (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                  hsame row M ∨ hsame row selectorRead ∨ hsame row readyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont K F radiusRead ∧
                  Cont radiusRead rho selectorRead ∧ Cont selectorRead M readyRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle readyRead pkg)
              hsame ∧
            UnaryHistory selectorRead ∧ UnaryHistory readyRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM selectorRoute readyRoute readyPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, radiusRoute, _handoffRoute,
    pkgP, _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed radiusUnary unaryRho selectorRoute
  have readyUnary : UnaryHistory readyRead :=
    unary_cont_closed selectorUnary unaryM readyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row selectorRead ∨ hsame row readyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho selectorRead ∧
              Cont selectorRead M readyRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle readyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readyRead ⟨hsame_refl readyRead, readyUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, radiusRoute, selectorRoute, readyRoute, pkgP, readyPkg⟩
  }
  exact ⟨cert, selectorUnary, readyUnary⟩

end BEDC.Derived.EquicontinuityUp
