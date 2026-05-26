import BEDC.Derived.CauchySequenceBoundedUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchySequenceBoundedUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceBoundedCarrier_dyadic_bound_stability [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      transportedBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      hsame bound transportedBound ->
        PkgSig bundle transportedBound pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory transportedBound ∧ hsame bound transportedBound ∧
              PkgSig bundle name pkg ∧ PkgSig bundle transportedBound pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier boundSame transportedBoundPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, _routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, _toleranceBoundReadback,
    _readbackRouteSeal, _provenanceTransportName, namePkg⟩ := carrier
  have transportedBoundUnary : UnaryHistory transportedBound :=
    unary_transport boundUnary boundSame
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, transportedBoundUnary, boundSame, namePkg,
      transportedBoundPkg⟩

theorem CauchySequenceBoundedCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      ledgerRead escapedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            PkgSig bundle escapedRead pkg ->
              UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                UnaryHistory bound ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                  UnaryHistory provenance ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory escapedRead ∧ Cont schedule modulus tolerance ∧
                      Cont tolerance bound readback ∧ Cont provenance transport name ∧
                        Cont bound transport ledgerRead ∧ Cont ledgerRead route escapedRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle escapedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, _readbackRouteSeal,
    provenanceTransportName, namePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, transportUnary, routeUnary,
      provenanceUnary, ledgerReadUnary, escapedReadUnary, scheduleModulusTolerance,
      toleranceBoundReadback, provenanceTransportName, boundTransportLedger, ledgerRouteEscaped,
      namePkg, escapedPkg⟩

theorem CauchySequenceBoundedCarrier_scoped_dependency_surface [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name ledgerRead
      escapedRead sealedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            Cont escapedRead realSeal sealedConsumer ->
              PkgSig bundle sealedConsumer pkg ->
                UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                  UnaryHistory bound ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                    UnaryHistory provenance ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory escapedRead ∧ UnaryHistory sealedConsumer ∧
                        Cont schedule modulus tolerance ∧ Cont tolerance bound readback ∧
                          Cont readback route realSeal ∧ Cont provenance transport name ∧
                            Cont bound transport ledgerRead ∧
                              Cont ledgerRead route escapedRead ∧
                                Cont escapedRead realSeal sealedConsumer ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle sealedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedSealConsumer
    sealedConsumerPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  have sealedConsumerUnary : UnaryHistory sealedConsumer :=
    unary_cont_closed escapedReadUnary realSealUnary escapedSealConsumer
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, transportUnary, routeUnary,
      provenanceUnary, ledgerReadUnary, escapedReadUnary, sealedConsumerUnary,
      scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
      provenanceTransportName, boundTransportLedger, ledgerRouteEscaped, escapedSealConsumer,
      namePkg, sealedConsumerPkg⟩

theorem CauchySequenceBoundedCarrier_bridge_surface [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name ledgerRead
      escapedRead sealedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            Cont escapedRead realSeal sealedConsumer ->
              PkgSig bundle sealedConsumer pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealedConsumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row bound ∨ hsame row ledgerRead ∨ hsame row escapedRead ∨
                        hsame row sealedConsumer ∨ Cont bound transport ledgerRead ∨
                          Cont ledgerRead route escapedRead ∨
                            Cont escapedRead realSeal sealedConsumer)
                    (fun row : BHist =>
                      PkgSig bundle name pkg ∧ PkgSig bundle sealedConsumer pkg ∧
                        hsame row sealedConsumer)
                    hsame ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory escapedRead ∧
                    UnaryHistory sealedConsumer ∧ Cont bound transport ledgerRead ∧
                      Cont ledgerRead route escapedRead ∧
                        Cont escapedRead realSeal sealedConsumer ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle sealedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedSealConsumer
    sealedConsumerPkg
  obtain ⟨_scheduleUnary, _modulusUnary, toleranceUnary, boundUnary, routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    _provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  have sealedConsumerUnary : UnaryHistory sealedConsumer :=
    unary_cont_closed escapedReadUnary realSealUnary escapedSealConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedConsumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row ledgerRead ∨ hsame row escapedRead ∨
              hsame row sealedConsumer ∨ Cont bound transport ledgerRead ∨
                Cont ledgerRead route escapedRead ∨ Cont escapedRead realSeal sealedConsumer)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle sealedConsumer pkg ∧
              hsame row sealedConsumer)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealedConsumer ⟨hsame_refl sealedConsumer, sealedConsumerUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨namePkg, sealedConsumerPkg, sourceRow.left⟩
    }
  exact
    ⟨cert, ledgerReadUnary, escapedReadUnary, sealedConsumerUnary, boundTransportLedger,
      ledgerRouteEscaped, escapedSealConsumer, namePkg, sealedConsumerPkg⟩

theorem CauchySequenceBoundedCarrier_mature_consumer_grid [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name ledgerRead
      escapedRead sealedConsumer completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            Cont escapedRead realSeal sealedConsumer ->
              Cont sealedConsumer realSeal completionRead ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                    UnaryHistory bound ∧ UnaryHistory ledgerRead ∧ UnaryHistory escapedRead ∧
                      UnaryHistory sealedConsumer ∧ UnaryHistory completionRead ∧
                        Cont bound transport ledgerRead ∧ Cont ledgerRead route escapedRead ∧
                          Cont escapedRead realSeal sealedConsumer ∧
                            Cont sealedConsumer realSeal completionRead ∧
                              PkgSig bundle name pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedSealConsumer
    sealedConsumerRealSealCompletion completionReadPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    _provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  have sealedConsumerUnary : UnaryHistory sealedConsumer :=
    unary_cont_closed escapedReadUnary realSealUnary escapedSealConsumer
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealedConsumerUnary realSealUnary sealedConsumerRealSealCompletion
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, ledgerReadUnary,
      escapedReadUnary, sealedConsumerUnary, completionReadUnary, boundTransportLedger,
      ledgerRouteEscaped, escapedSealConsumer, sealedConsumerRealSealCompletion, namePkg,
      completionReadPkg⟩

theorem CauchySequenceBoundedCarrier_completion_consumer_example [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name ledgerRead
      escapedRead sealedConsumer completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            Cont escapedRead realSeal sealedConsumer ->
              Cont sealedConsumer realSeal completionRead ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        Cont bound transport ledgerRead ∨ Cont ledgerRead route escapedRead ∨
                          Cont escapedRead realSeal sealedConsumer ∨
                            Cont sealedConsumer realSeal completionRead)
                      (fun row : BHist =>
                        PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg ∧
                          hsame row completionRead)
                      hsame ∧
                    UnaryHistory completionRead ∧ Cont sealedConsumer realSeal completionRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedSealConsumer
    sealedConsumerRealSealCompletion completionReadPkg
  obtain ⟨_scheduleUnary, _modulusUnary, toleranceUnary, boundUnary, routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    _provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  have sealedConsumerUnary : UnaryHistory sealedConsumer :=
    unary_cont_closed escapedReadUnary realSealUnary escapedSealConsumer
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealedConsumerUnary realSealUnary sealedConsumerRealSealCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont bound transport ledgerRead ∨ Cont ledgerRead route escapedRead ∨
              Cont escapedRead realSeal sealedConsumer ∨
                Cont sealedConsumer realSeal completionRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg ∧
              hsame row completionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row _sourceRow
        exact Or.inr (Or.inr (Or.inr sealedConsumerRealSealCompletion))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨namePkg, completionReadPkg, sourceRow.left⟩
    }
  exact
    ⟨cert, completionReadUnary, sealedConsumerRealSealCompletion, namePkg, completionReadPkg⟩

end BEDC.Derived.CauchySequenceBoundedUp
