import BEDC.Derived.EquicontinuityUp.UniformModulusConsumerBoundary

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityArzelaAscoliBoundaryReadiness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteNetRead arzelaRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          UnaryHistory R ->
            Cont handoffRead M modulusRead ->
              Cont modulusRead T finiteNetRead ->
                Cont finiteNetRead R arzelaRead ->
                  Cont arzelaRead N boundaryRead ->
                    PkgSig bundle boundaryRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                              hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row N ∨
                                hsame row boundaryRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont K F radiusRead ∧
                              Cont radiusRead rho handoffRead ∧
                                Cont handoffRead M modulusRead ∧
                                  Cont modulusRead T finiteNetRead ∧
                                    Cont finiteNetRead R arzelaRead ∧
                                      Cont arzelaRead N boundaryRead ∧
                                        PkgSig bundle boundaryRead pkg)
                          hsame ∧
                        UnaryHistory modulusRead ∧ UnaryHistory finiteNetRead ∧
                          UnaryHistory arzelaRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryT unaryR modulusRoute finiteNetRoute arzelaRoute boundaryRoute
    boundaryPkg
  have sharedStability :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨_unaryK, _unaryF, _unaryRho, _unaryCarrierR, unaryN, _compactFamily,
    _radiusHandoff, _carrierPkgP, _carrierPkgN⟩ := carrier
  obtain ⟨_radiusUnary, handoffUnary, radiusRoute, handoffRoute, _pkgP, _pkgN⟩ :=
    sharedStability
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM modulusRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed modulusUnary unaryT finiteNetRoute
  have arzelaUnary : UnaryHistory arzelaRead :=
    unary_cont_closed finiteNetUnary unaryR arzelaRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed arzelaUnary unaryN boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row R ∨ hsame row N ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              Cont handoffRead M modulusRead ∧ Cont modulusRead T finiteNetRead ∧
                Cont finiteNetRead R arzelaRead ∧ Cont arzelaRead N boundaryRead ∧
                  PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        ⟨source.right, radiusRoute, handoffRoute, modulusRoute, finiteNetRoute,
          arzelaRoute, boundaryRoute, boundaryPkg⟩
  }
  exact ⟨cert, modulusUnary, finiteNetUnary, arzelaUnary, boundaryUnary⟩

theorem EquicontinuityUniformModulusConsumerBoundary_arzela_namecert
    [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteNetRead arzelaRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          UnaryHistory R ->
            Cont handoffRead M modulusRead ->
              Cont modulusRead T finiteNetRead ->
                Cont finiteNetRead R arzelaRead ->
                  Cont arzelaRead N boundaryRead ->
                    PkgSig bundle finiteNetRead pkg ->
                      PkgSig bundle boundaryRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row F ∨ hsame row eps ∨
                                hsame row rho ∨ hsame row M ∨ hsame row T ∨
                                  hsame row R ∨ hsame row N ∨ hsame row finiteNetRead ∨
                                    hsame row boundaryRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont K F radiusRead ∧
                                Cont radiusRead rho handoffRead ∧
                                  Cont handoffRead M modulusRead ∧
                                    Cont modulusRead T finiteNetRead ∧
                                      Cont finiteNetRead R arzelaRead ∧
                                        Cont arzelaRead N boundaryRead ∧
                                          PkgSig bundle finiteNetRead pkg ∧
                                            PkgSig bundle boundaryRead pkg)
                            hsame ∧ UnaryHistory finiteNetRead ∧
                          UnaryHistory arzelaRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryT unaryR modulusRoute finiteNetRoute arzelaRoute boundaryRoute
    finiteNetPkg boundaryPkg
  obtain ⟨_radiusUnary, _handoffUnary, _modulusUnary, finiteNetUnary, radiusRoute,
    handoffRoute, modulusRouteOut, finiteNetRouteOut, _pkgP, finiteNetPkgOut⟩ :=
    EquicontinuityCarrier_uniform_modulus_consumer_boundary carrier unaryM unaryT
      modulusRoute finiteNetRoute finiteNetPkg
  obtain ⟨_unaryK, _unaryF, _unaryRho, _unaryCarrierR, unaryN, _compactFamily,
    _radiusHandoff, _carrierPkgP, _carrierPkgN⟩ := carrier
  have arzelaUnary : UnaryHistory arzelaRead :=
    unary_cont_closed finiteNetUnary unaryR arzelaRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed arzelaUnary unaryN boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
              hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row N ∨
                hsame row finiteNetRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              Cont handoffRead M modulusRead ∧ Cont modulusRead T finiteNetRead ∧
                Cont finiteNetRead R arzelaRead ∧ Cont arzelaRead N boundaryRead ∧
                  PkgSig bundle finiteNetRead pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        ⟨source.right, radiusRoute, handoffRoute, modulusRouteOut, finiteNetRouteOut,
          arzelaRoute, boundaryRoute, finiteNetPkgOut, boundaryPkg⟩
  }
  exact ⟨cert, finiteNetUnary, arzelaUnary, boundaryUnary⟩

theorem EquicontinuityFamilyModulusConsumerExhaustion_arzela_terminal
    [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyRead consumerRead arzelaRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory N ->
          UnaryHistory T ->
            Cont radiusRead rho familyRead ->
              Cont familyRead M handoffRead ->
                Cont handoffRead R consumerRead ->
                  Cont consumerRead N arzelaRead ->
                    Cont arzelaRead T terminalRead ->
                      PkgSig bundle consumerRead pkg ->
                        PkgSig bundle terminalRead pkg ->
                          SemanticNameCert
                            (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                                hsame row R ∨ hsame row N ∨ hsame row T ∨
                                  hsame row familyRead ∨ hsame row consumerRead ∨
                                    hsame row terminalRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont K F radiusRead ∧
                                Cont radiusRead rho familyRead ∧
                                  Cont familyRead M handoffRead ∧
                                    Cont handoffRead R consumerRead ∧
                                      Cont consumerRead N arzelaRead ∧
                                        Cont arzelaRead T terminalRead ∧
                                          PkgSig bundle consumerRead pkg ∧
                                            PkgSig bundle terminalRead pkg)
                            hsame ∧ UnaryHistory familyRead ∧ UnaryHistory consumerRead ∧
                          UnaryHistory arzelaRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryN unaryT radiusFamily familyHandoff handoffConsumer consumerArzela
    arzelaTerminal consumerPkg terminalPkg
  obtain ⟨_radiusUnary, familyUnary, _handoffUnary, consumerUnary, radiusRoute,
    radiusFamilyOut, familyHandoffOut, handoffConsumerOut, _pkgP, consumerPkgOut⟩ :=
    EquicontinuityCarrier_family_modulus_consumer_exhaustion carrier unaryM radiusFamily
      familyHandoff handoffConsumer consumerPkg
  obtain ⟨_unaryK, _unaryF, _unaryRho, _unaryCarrierR, _unaryCarrierN,
    _compactFamily, _radiusHandoff, _carrierPkgP, _carrierPkgN⟩ := carrier
  have arzelaUnary : UnaryHistory arzelaRead :=
    unary_cont_closed consumerUnary unaryN consumerArzela
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed arzelaUnary unaryT arzelaTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨ hsame row R ∨
              hsame row N ∨ hsame row T ∨ hsame row familyRead ∨
                hsame row consumerRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho familyRead ∧
              Cont familyRead M handoffRead ∧ Cont handoffRead R consumerRead ∧
                Cont consumerRead N arzelaRead ∧ Cont arzelaRead T terminalRead ∧
                  PkgSig bundle consumerRead pkg ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact
        ⟨source.right, radiusRoute, radiusFamilyOut, familyHandoffOut,
          handoffConsumerOut, consumerArzela, arzelaTerminal, consumerPkgOut,
          terminalPkg⟩
  }
  exact ⟨cert, familyUnary, consumerUnary, arzelaUnary, terminalUnary⟩

end BEDC.Derived.EquicontinuityUp
