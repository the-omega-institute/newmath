import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VonneumannalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VonNeumannAlgBHistCarrier [AskSetup] [PackageSetup]
    (cstar hilbert operator adjoint multiplication weakTest weakProbe provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cstar ∧ UnaryHistory hilbert ∧ UnaryHistory operator ∧
    UnaryHistory adjoint ∧ UnaryHistory multiplication ∧ UnaryHistory weakTest ∧
      UnaryHistory weakProbe ∧ UnaryHistory provenance ∧ Cont cstar operator adjoint ∧
        Cont operator multiplication provenance ∧ Cont hilbert weakProbe weakTest ∧
          Cont weakTest operator endpoint ∧ PkgSig bundle endpoint pkg

theorem VonNeumannAlgBHistCarrier_weak_operator_ledger_exactness [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakTest weakProbe provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest weakProbe
        provenance endpoint bundle pkg ->
      UnaryHistory weakTest ∧ UnaryHistory weakProbe ∧ Cont hilbert weakProbe weakTest ∧
        Cont weakTest operator endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have weakTestUnary : UnaryHistory weakTest :=
    carrier.right.right.right.right.right.left
  have weakProbeUnary : UnaryHistory weakProbe :=
    carrier.right.right.right.right.right.right.left
  have weakProbeRow : Cont hilbert weakProbe weakTest :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont weakTest operator endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have packageRow : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro weakTestUnary
    (And.intro weakProbeUnary
      (And.intro weakProbeRow (And.intro endpointRow packageRow)))

theorem VonNeumannAlgBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakTest weakProbe provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
        weakProbe provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont cstar operator adjoint ∧ Cont operator multiplication provenance ∧
          Cont hilbert weakProbe weakTest ∧ Cont weakTest operator endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrierData
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
            weakProbe provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrierData (hsame_refl endpoint))
  obtain ⟨_cstarUnary, _hilbertUnary, _operatorUnary, _adjointUnary,
    _multiplicationUnary, _weakTestUnary, _weakProbeUnary, _provenanceUnary,
    cstarOperatorRow, operatorMultiplicationRow, weakProbeRow, weakTestRow, packageRow⟩ :=
    carrierData
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest
                weakProbe provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro cstarOperatorRow
      (And.intro operatorMultiplicationRow
        (And.intro weakProbeRow (And.intro weakTestRow packageRow))))

def VonneumannalgebraBHistCarrier [AskSetup] [PackageSetup]
    (cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cstar ∧ UnaryHistory hilbert ∧ UnaryHistory operator ∧
    UnaryHistory adjoint ∧ UnaryHistory multiplication ∧ UnaryHistory weakProbe ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧
        Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
          Cont weakProbe transport endpoint ∧ PkgSig bundle endpoint pkg

theorem VonneumannalgebraBHistCarrier_obligation_surface [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
          Cont weakProbe transport endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrierData
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
            weakProbe transport provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrierData (hsame_refl endpoint))
  obtain ⟨_cstarUnary, _hilbertUnary, _operatorUnary, _adjointUnary,
    _multiplicationUnary, _weakProbeUnary, _transportUnary, _provenanceUnary,
    cstarHilbertRow, operatorAdjointRow, weakTransportRow, packageRow⟩ := carrierData
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
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
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro cstarHilbertRow
      (And.intro operatorAdjointRow (And.intro weakTransportRow packageRow)))

theorem VonneumannalgebraBHistCarrier_weak_operator_ledger_exactness [AskSetup]
    [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint
      weakEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      Cont weakProbe hilbert weakEndpoint ->
      UnaryHistory weakEndpoint ∧ hsame weakEndpoint (append weakProbe hilbert) ∧
        Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
          Cont weakProbe transport endpoint ∧ Cont weakProbe hilbert weakEndpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier weakRow
  obtain ⟨cstarUnary, hilbertUnary, _operatorUnary, _adjointUnary, _multiplicationUnary,
    weakProbeUnary, _transportUnary, _provenanceUnary, cstarHilbertRow,
    operatorAdjointRow, weakTransportRow, packageRow⟩ := carrier
  have weakEndpointUnary : UnaryHistory weakEndpoint :=
    unary_cont_closed weakProbeUnary hilbertUnary weakRow
  exact And.intro weakEndpointUnary
      (And.intro weakRow
        (And.intro cstarHilbertRow
          (And.intro operatorAdjointRow
            (And.intro weakTransportRow (And.intro weakRow packageRow)))))

theorem VonneumannalgebraBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint
      weakEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      Cont weakProbe hilbert weakEndpoint ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        UnaryHistory weakEndpoint ∧ Cont cstar hilbert operator ∧
          Cont operator adjoint multiplication ∧ Cont weakProbe transport endpoint ∧
            Cont weakProbe hilbert weakEndpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrierData weakEndpointRow
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
            weakProbe transport provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrierData (hsame_refl endpoint))
  obtain ⟨_cstarUnary, hilbertUnary, _operatorUnary, _adjointUnary,
    _multiplicationUnary, weakProbeUnary, _transportUnary, _provenanceUnary,
    cstarHilbertRow, operatorAdjointRow, weakTransportRow, packageRow⟩ := carrierData
  have weakEndpointUnary : UnaryHistory weakEndpoint :=
    unary_cont_closed weakProbeUnary hilbertUnary weakEndpointRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication
                weakProbe transport provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
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
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro weakEndpointUnary
      (And.intro cstarHilbertRow
        (And.intro operatorAdjointRow
          (And.intro weakTransportRow (And.intro weakEndpointRow packageRow)))))

theorem VonneumannalgebraBHistCarrier_star_operation_stability [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint cstar'
      hilbert' adjoint' weakProbe' transport' provenance' operator' multiplication' endpoint' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      hsame cstar cstar' ->
        hsame hilbert hilbert' ->
          hsame adjoint adjoint' ->
            hsame weakProbe weakProbe' ->
              hsame transport transport' ->
                hsame provenance provenance' ->
                  Cont cstar' hilbert' operator' ->
                    Cont operator' adjoint' multiplication' ->
                      Cont weakProbe' transport' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          VonneumannalgebraBHistCarrier cstar' hilbert' operator' adjoint'
                              multiplication' weakProbe' transport' provenance' endpoint' bundle
                              pkg ∧
                            hsame operator operator' ∧ hsame multiplication multiplication' ∧
                              hsame endpoint endpoint' := by
  intro carrier sameCstar sameHilbert sameAdjoint sameWeakProbe sameTransport sameProvenance
    cstarHilbertRow' operatorAdjointRow' weakTransportRow' packageRow'
  obtain ⟨cstarUnary, hilbertUnary, _operatorUnary, adjointUnary, _multiplicationUnary,
    weakProbeUnary, transportUnary, provenanceUnary, cstarHilbertRow, operatorAdjointRow,
    weakTransportRow, _packageRow⟩ := carrier
  have cstarUnary' : UnaryHistory cstar' :=
    unary_transport cstarUnary sameCstar
  have hilbertUnary' : UnaryHistory hilbert' :=
    unary_transport hilbertUnary sameHilbert
  have adjointUnary' : UnaryHistory adjoint' :=
    unary_transport adjointUnary sameAdjoint
  have weakProbeUnary' : UnaryHistory weakProbe' :=
    unary_transport weakProbeUnary sameWeakProbe
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have operatorUnary' : UnaryHistory operator' :=
    unary_cont_closed cstarUnary' hilbertUnary' cstarHilbertRow'
  have multiplicationUnary' : UnaryHistory multiplication' :=
    unary_cont_closed operatorUnary' adjointUnary' operatorAdjointRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed weakProbeUnary' transportUnary' weakTransportRow'
  have sameOperator : hsame operator operator' :=
    cont_respects_hsame sameCstar sameHilbert cstarHilbertRow cstarHilbertRow'
  have sameMultiplication : hsame multiplication multiplication' :=
    cont_respects_hsame sameOperator sameAdjoint operatorAdjointRow operatorAdjointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameWeakProbe sameTransport weakTransportRow weakTransportRow'
  exact And.intro
    (And.intro cstarUnary'
      (And.intro hilbertUnary'
        (And.intro operatorUnary'
          (And.intro adjointUnary'
            (And.intro multiplicationUnary'
              (And.intro weakProbeUnary'
                (And.intro transportUnary'
                  (And.intro provenanceUnary'
                    (And.intro cstarHilbertRow'
                      (And.intro operatorAdjointRow'
                        (And.intro weakTransportRow' packageRow')))))))))))
    (And.intro sameOperator (And.intro sameMultiplication sameEndpoint))

theorem VonneumannalgebraBHistCarrier_downstream_boundary [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      Cont endpoint weakProbe downstream ->
        UnaryHistory downstream ∧ Cont cstar hilbert operator ∧
          Cont operator adjoint multiplication ∧ Cont weakProbe transport endpoint ∧
            Cont endpoint weakProbe downstream ∧ PkgSig bundle endpoint pkg := by
  intro carrier downstreamRow
  obtain ⟨_cstarUnary, _hilbertUnary, _operatorUnary, _adjointUnary, _multiplicationUnary,
    weakProbeUnary, transportUnary, _provenanceUnary, cstarHilbertRow, operatorAdjointRow,
    weakTransportRow, packageRow⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weakProbeUnary transportUnary weakTransportRow
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed endpointUnary weakProbeUnary downstreamRow
  exact And.intro downstreamUnary
    (And.intro cstarHilbertRow
      (And.intro operatorAdjointRow
        (And.intro weakTransportRow (And.intro downstreamRow packageRow))))

theorem VonneumannalgebraBHistCarrier_finite_packet_rows [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint
      weakEndpoint downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      Cont weakProbe hilbert weakEndpoint ->
        Cont endpoint weakProbe downstream ->
          UnaryHistory cstar ∧ UnaryHistory hilbert ∧ UnaryHistory weakEndpoint ∧
            UnaryHistory downstream ∧ hsame weakEndpoint (append weakProbe hilbert) ∧
              Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
                Cont weakProbe transport endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier weakEndpointRow downstreamRow
  obtain ⟨cstarUnary, hilbertUnary, _operatorUnary, _adjointUnary, _multiplicationUnary,
    weakProbeUnary, transportUnary, _provenanceUnary, cstarHilbertRow, operatorAdjointRow,
    weakTransportRow, packageRow⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weakProbeUnary transportUnary weakTransportRow
  have weakEndpointUnary : UnaryHistory weakEndpoint :=
    unary_cont_closed weakProbeUnary hilbertUnary weakEndpointRow
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed endpointUnary weakProbeUnary downstreamRow
  exact ⟨cstarUnary, hilbertUnary, weakEndpointUnary, downstreamUnary, weakEndpointRow,
    cstarHilbertRow, operatorAdjointRow, weakTransportRow, packageRow⟩

end BEDC.Derived.VonneumannalgebraUp
