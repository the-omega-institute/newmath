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

end BEDC.Derived.VonneumannalgebraUp
